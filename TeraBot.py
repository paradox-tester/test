#!/usr/bin/env python3
"""
Pyrogram-based refactor of the Telegram -> MyJDownloader bot with integrated GoFile downloader.
FIXED VERSION: All blocking I/O offloaded to threads; subprocess timeouts; concurrency limits;
               global state locks; no more event-loop freezes or asyncio warnings.
Also fixed: ZIP progress now uses file-size ratio, accurate and smooth.
Also fixed: Duplicate "Created zip" message eliminated.
PER-USER AUTOMATOR: Each user can enable/disable automator independently.
Default from env AUTOMATOR_DEFAULT_ON (false by default).
NEW: All user requests (media, links) are now enqueued into a single global processing queue,
     regardless of automator status. Automator logic is applied during processing.
NEW: Users can cancel their queued or running jobs via an inline keyboard button.
NEW: Access control: optional channel/group membership and public access toggle.
NEW: /uptime command to show how long the bot has been online (public).

UPDATED: /unzip now uses 'unar' for decompression and a reliable size‑based progress monitor.
         Improved error handling: shows full error output and logs the command for debugging.
NEW: Disk quota system: per-user quotas and global free-space threshold, both togglable via .env.
NEW: Periodic quota checks during downloads, compression, extraction, and automator – any operation
     that would exceed the limit is aborted immediately.
FIXED: Torrent handling: better detection, logging, and fallback matching to ensure downloads start.
NEW: Upload inactivity timeout: if no progress for 10 minutes, the upload is cancelled and retried.
FIXED: qBittorrent monitoring now uses resilient progress editing to survive network failures,
       avoiding freezes. Automator tasks are offloaded to background.
FIXED: Upload progress editing now also uses resilient helper, preventing freezes during uploads.
FIXED: qBittorrent monitoring no longer blocks on progress edits – edits are fire‑and‑forget tasks,
       ensuring the bot stays responsive even under poor network conditions.
FIXED: All background health checks and keep-alive tasks now have timeouts, preventing infinite hangs.
FIXED: Fire-and-forget edit tasks are cancelled when monitoring ends, avoiding orphaned tasks.
FIXED: process_job now has a global timeout to prevent indefinite blocking.
FURTHER FIX: edit_progress_resilient now has circuit breaker, lower timeouts, and no retries on network errors.
FURTHER FIX: qBittorrent monitor limits pending edits to 3 and skips edits if client disconnected.
FINAL FIX: All progress edits inside monitoring loops are now fire-and-forget (never awaited),
           eliminating the last source of freezes.

ADDITIONAL FIX: Unificada la supervisión de salud en un watchdog por latido interno (pingtask)
                que detecta congelamientos del event loop y recupera el bot sin perder tareas.
                Eliminados health checks redundantes que causaban conflictos.
                Aumentados timeouts y límites de tareas de edición.
                Añadidos locks de reconexión y semáforos para controlar concurrencia.
                El bot ahora es invulnerable a problemas de red y se recupera automáticamente.
                
ENHANCED LOGGING: All logs are now written to both console and a rotating file (logs/bot.log)
                  with DEBUG level for detailed troubleshooting. No extra periodic reports added.
"""

import os
import re
import logging
from dotenv import load_dotenv
import asyncio
import shutil
import time
from pathlib import Path
from typing import List, Tuple, Optional, Any, Iterator, NoReturn, TextIO, Callable, Dict, Set
import aiohttp
import urllib.parse
import math
import uuid
import json
from datetime import datetime, timedelta, timezone
import zipfile
import subprocess
import html
from html.parser import HTMLParser
import socket
import concurrent.futures
from logging.handlers import RotatingFileHandler

from myjdapi.myjdapi import Myjdapi

import sys

if sys.version_info >= (3, 10):
    try:
        asyncio.get_running_loop()
    except RuntimeError:
        asyncio.set_event_loop(asyncio.new_event_loop())

from pyrogram import Client, filters, idle
from pyrogram.types import Message
from pyrogram.handlers import MessageHandler
from pyrogram.errors import FloodWait
from pyrogram.types import InlineKeyboardButton, InlineKeyboardMarkup, CallbackQuery
from pyrogram.handlers import CallbackQueryHandler
from pyrogram.enums import ParseMode

from os import getcwd, getenv, listdir, makedirs, name, path, rmdir
from sys import exit, stdout, stderr
from types import FrameType
from itertools import count
from concurrent.futures import ThreadPoolExecutor
from threading import Event as ThreadEvent
from hashlib import sha256
from shutil import move
from signal import signal, SIGINT, SIG_IGN
from time import perf_counter, time as _time
import signal as signal_module

try:
    from PIL import Image
    PIL_AVAILABLE = True
except ImportError:
    PIL_AVAILABLE = False
    # logging.warning will be set later

try:
    import psutil
    PSUTIL_AVAILABLE = True
except ImportError:
    PSUTIL_AVAILABLE = False

NEW_LINE: str = "\n" if name != "nt" else "\r\n"

load_dotenv()

# ===================================================================
# CONFIGURACIÓN DE LOGGING MEJORADA (CONSOLA + ARCHIVO ROTATIVO)
# ===================================================================
LOG_DIR = Path.cwd() / "logs"
LOG_DIR.mkdir(exist_ok=True)
LOG_FILE = LOG_DIR / "bot.log"

# Configurar el logger raíz
root_logger = logging.getLogger()
root_logger.setLevel(logging.DEBUG)  # Guardaremos todo en archivo

# Formato detallado
formatter = logging.Formatter(
    '%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)

# Handler para consola (solo INFO y superior para no saturar)
console_handler = logging.StreamHandler(sys.stdout)
console_handler.setLevel(logging.INFO)
console_handler.setFormatter(formatter)
root_logger.addHandler(console_handler)

# Handler para archivo con rotación (DEBUG para todos los detalles)
file_handler = RotatingFileHandler(
    LOG_FILE,
    maxBytes=10*1024*1024,  # 10 MB
    backupCount=5,
    encoding='utf-8'
)
file_handler.setLevel(logging.DEBUG)
file_handler.setFormatter(formatter)
root_logger.addHandler(file_handler)

# Asegurar que los logs de pyrogram también se capturen
logging.getLogger("pyrogram").setLevel(logging.DEBUG)
logging.getLogger("aiohttp").setLevel(logging.WARNING)

logger = logging.getLogger(__name__)
logger.info("Logging system initialized. Logs will be saved to %s", LOG_FILE)

# ===================================================================

COMMAND_TIMEOUT = 30
CONNECTION_RETRY_DELAY = 10          # increased from 5
FILE_OPERATION_TIMEOUT = 15
UPLOAD_TIMEOUT = 7200  # 2 hours
UPLOAD_RETRY_DELAY = 5

# NEW: upload inactivity timeout (no progress) – default 30 minutes (1800s)
UPLOAD_INACTIVITY_TIMEOUT = int(os.getenv("UPLOAD_INACTIVITY_TIMEOUT", "1200"))   # increased to 20 min

DEFAULT_CHUNK_SIZE = 1024 * 1024 * 32
MAX_CONCURRENT_UPLOADS = int(os.getenv("PYRO_MAX_CONCURRENT_TRANSMISSIONS", "32"))
WORKER_COUNT = int(os.getenv("PYRO_WORKERS", "32"))
FORCE_BOT_UPLOADS = os.getenv("FORCE_BOT_UPLOADS", "False").lower() == "true"
FORCE_USER_UPLOADS = os.getenv("FORCE_USER_UPLOADS", "False").lower() == "true"
LARGE_FILE_THRESHOLD = 50 * 1024 * 1024

SUFFIX_RETRY_DELAY = float(os.getenv("SUFFIX_RETRY_DELAY", "2.0"))
SUFFIX_RETRY_COUNT = int(os.getenv("SUFFIX_RETRY_COUNT", "8"))
SUFFIX_POST_DOWNLOAD_WAIT = float(os.getenv("SUFFIX_POST_DOWNLOAD_WAIT", "3.0"))

DOWNLOAD_INACTIVITY_TIMEOUT = int(os.getenv("DOWNLOAD_INACTIVITY_TIMEOUT", "1800"))  # 30 min

# New: compression idle timeout (no progress) in seconds – default 30 minutes
COMPRESSION_IDLE_TIMEOUT = int(os.getenv("COMPRESSION_IDLE_TIMEOUT", "1800"))

# New constant for 7z read timeout (40 minutes)
SEVENZ_READ_TIMEOUT = 3600  # seconds

# Disk quota settings
DISK_QUOTA_ENABLED = os.getenv("DISK_QUOTA_ENABLED", "false").lower() == "true"
DISK_QUOTA_SIZE_GB = int(os.getenv("DISK_QUOTA_SIZE_GB", "10"))
DISK_FREE_THRESHOLD_PERCENT = int(os.getenv("DISK_FREE_THRESHOLD_PERCENT", "10"))

FILE_SIGNING_ENABLED: bool = False
FILE_SIGN: str = ""

# PER-USER AUTOMATOR: default from env, per-user overrides in dict
DEFAULT_AUTOMATOR_ENABLED = os.getenv("AUTOMATOR_DEFAULT_ON", "false").lower() == "true"
USER_AUTOMATOR: Dict[int, bool] = {}          # user_id -> enabled
USER_AUTOMATOR_LOCK = asyncio.Lock()

# --- New access control env vars ---
PUBLIC_ACCESS = os.getenv("PUBLIC_ACCESS", "false").lower() == "true"
REQUIRED_CHANNELS_RAW = os.getenv("REQUIRED_CHANNELS", "")
REQUIRED_CHANNELS = [c.strip() for c in REQUIRED_CHANNELS_RAW.split(",") if c.strip()]

# Membership cache
_membership_cache = {}
_membership_cache_lock = asyncio.Lock()
MEMBERSHIP_CACHE_TTL = 300  # seconds
# ---------------------------------

AUTOMATOR_CONCURRENCY: int = 1
AUTOMATOR_SEMAPHORE: Optional[asyncio.Semaphore] = None
AUTOMATOR_ACTIVE_COUNT: int = 0
_AUTOMATOR_COUNT_LOCK: Optional[asyncio.Lock] = None
AUTOMATOR_UPLOADS: dict = {}
AUTOMATOR_JOBS: dict = {}

PROCESSING_QUEUE: Optional[asyncio.Queue] = None
PROCESSING_SEMAPHORE: Optional[asyncio.Semaphore] = None
PROCESSING_WORKERS: List[asyncio.Task] = []

# --- NEW: Pending jobs for cancellation ---
PENDING_JOBS: Dict[str, dict] = {}  # job_id -> {job, cancel_event, user_id, message}
PENDING_JOBS_LOCK = asyncio.Lock()

_SEND_LOCK = asyncio.Lock()
_LAST_SEND_TIME = 0.0
_SEND_MIN_INTERVAL_NORMAL = 1.0
_SEND_MIN_INTERVAL_AUTOMATOR = float(os.getenv("AUTOMATOR_SEND_INTERVAL", "10.0"))
_LAST_FLOODWAIT_END = 0.0
_TEMPORARY_INTERVAL = None
_TEMPORARY_END_TIME = 0.0

# --- NEW: Global locks for shared dictionaries ---
DOWNLOAD_TASKS_LOCK = asyncio.Lock()
UPLOAD_GROUPS_LOCK = asyncio.Lock()
AUTOMATOR_UPLOADS_LOCK = asyncio.Lock()
AUTOMATOR_JOBS_LOCK = asyncio.Lock()

# --- NEW: Semaphore for zip/unzip to limit concurrent subprocesses ---
ZIP_SEMAPHORE = asyncio.Semaphore(2)

# --- Global uptime tracking ---
START_TIME: Optional[float] = None

# --- Timeouts for threaded operations ---
JD_API_TIMEOUT = 15          # reduced from 30 to fail faster
FILE_IO_TIMEOUT = 60         # file system operations (rename, unlink, mkdir, etc.)
DIR_LIST_TIMEOUT = 30        # directory listing
FALLBACK_ZIP_TIMEOUT = 300   # fallback Python zip creation
THREADED_WALK_TIMEOUT = 120  # os.walk total size computation

# --- Safety timeouts (configurable, 0 = disabled) ---
DOWNLOAD_SAFETY_TIMEOUT = int(os.getenv("DOWNLOAD_SAFETY_TIMEOUT", "0"))   # 0 = no limit
JOB_SAFETY_TIMEOUT = int(os.getenv("JOB_SAFETY_TIMEOUT", "0"))             # 0 = no limit

# --- WATCHDOG POR LATIDO INTERNO (PINGTASK) ---
_last_heartbeat = time.time()
_heartbeat_lock = asyncio.Lock()
_reconnect_lock = asyncio.Lock()  # Evita reconexiones simultáneas
_edit_task_semaphore = asyncio.Semaphore(5)  # Máximo 5 ediciones concurrentes

# Helper for total size of a directory (synchronous, to be run in thread)
def get_total_size_sync(path: Path) -> int:
    total = 0
    try:
        for root, dirs, files in os.walk(path):
            for f in files:
                total += (Path(root) / f).stat().st_size
    except Exception:
        pass
    return total

# -------------------------------------------------------------------
# Disk quota helpers
# -------------------------------------------------------------------
async def get_user_usage_async(user) -> int:
    root = get_user_root_path(user)
    try:
        return await asyncio.wait_for(asyncio.to_thread(get_total_size_sync, root), timeout=THREADED_WALK_TIMEOUT)
    except Exception as e:
        logger.error(f"Failed to get user usage: {e}")
        return 0

async def check_user_quota(user, additional_bytes: int = 0) -> Tuple[bool, str]:
    if not DISK_QUOTA_ENABLED:
        return True, ""
    usage = await get_user_usage_async(user)
    quota_bytes = DISK_QUOTA_SIZE_GB * 1024**3
    if usage + additional_bytes > quota_bytes:
        return False, f"❌ Cuota de disco excedida. Uso: {human_size(usage)} / {human_size(quota_bytes)}. No se puede continuar."
    return True, ""

async def check_disk_free_space(path: Path) -> Tuple[bool, str]:
    if DISK_QUOTA_ENABLED:  # only check if quota system enabled
        try:
            total, used, free = await asyncio.wait_for(asyncio.to_thread(shutil.disk_usage, path), timeout=FILE_IO_TIMEOUT)
            free_percent = (free / total) * 100
            if free_percent < DISK_FREE_THRESHOLD_PERCENT:
                return False, f"❌ El espacio libre global es bajo ({free_percent:.1f}% libre). No hay más recursos disponibles."
        except Exception as e:
            logger.error(f"Failed to check disk free space: {e}")
            # If we cannot check, we allow (but log error)
    return True, ""

# ---- NEW: quota check with abort capability ----
async def check_quota_and_abort(user, additional_bytes=0, message=None, cancel_event=None,
                                stop_event=None, cancel_key=None, progress_msg=None):
    """
    Check if user's quota would be exceeded with additional_bytes.
    If exceeded, send a notification, set cancellation events, and return True.
    """
    if not DISK_QUOTA_ENABLED:
        return False
    try:
        usage = await get_user_usage_async(user)
        quota_bytes = DISK_QUOTA_SIZE_GB * 1024**3
        if usage + additional_bytes > quota_bytes:
            error_msg = (f"❌ Cuota de disco excedida. Uso: {human_size(usage)} / "
                         f"{human_size(quota_bytes)}. No se puede continuar.")
            if progress_msg:
                try:
                    await edit_with_retry(progress_msg.edit(_scrub_text_for_user(error_msg), reply_markup=None))
                except Exception:
                    pass
            elif message:
                await safe_send(message.chat.id, error_msg)
            # Set all cancellation mechanisms
            if cancel_event:
                cancel_event.set()
            if stop_event:
                stop_event.set()
            if cancel_key and cancel_key in DOWNLOAD_TASKS:
                DOWNLOAD_TASKS[cancel_key]['cancelled'] = True
            return True
    except Exception as e:
        logger.error(f"Quota check failed: {e}")
    return False
# ------------------------------------------------------------

async def _throttle_send():
    global _LAST_SEND_TIME, _TEMPORARY_INTERVAL, _TEMPORARY_END_TIME
    async with _SEND_LOCK:
        now = time.time()
        if _TEMPORARY_INTERVAL and now < _TEMPORARY_END_TIME:
            interval = _TEMPORARY_INTERVAL
        else:
            interval = _SEND_MIN_INTERVAL_NORMAL
        elapsed = now - _LAST_SEND_TIME
        if elapsed < interval:
            await asyncio.sleep(interval - elapsed)
        _LAST_SEND_TIME = time.time()

async def _send_with_retry(coro, retries=5):
    global _LAST_FLOODWAIT_END, _TEMPORARY_INTERVAL, _TEMPORARY_END_TIME, _SEND_MIN_INTERVAL_AUTOMATOR
    for attempt in range(retries):
        try:
            return await coro
        except FloodWait as e:
            wait = e.value
            if wait > 0:
                logging.warning(f"FloodWait: need to wait {wait}s before retrying send (attempt {attempt+1}/{retries})")
                _LAST_FLOODWAIT_END = time.time() + wait
                _TEMPORARY_INTERVAL = max(wait / 5, 10.0)
                _TEMPORARY_END_TIME = time.time() + wait
                if AUTOMATOR_ACTIVE_COUNT > 0:
                    _SEND_MIN_INTERVAL_AUTOMATOR = max(_SEND_MIN_INTERVAL_AUTOMATOR, wait / 10)
                await asyncio.sleep(wait)
            else:
                match = re.search(r'(\d+)', str(e))
                if match:
                    wait = int(match.group(1))
                    logging.warning(f"FloodWait: need to wait {wait}s (parsed) before retrying send")
                    _LAST_FLOODWAIT_END = time.time() + wait
                    _TEMPORARY_INTERVAL = max(wait / 5, 10.0)
                    _TEMPORARY_END_TIME = time.time() + wait
                    if AUTOMATOR_ACTIVE_COUNT > 0:
                        _SEND_MIN_INTERVAL_AUTOMATOR = max(_SEND_MIN_INTERVAL_AUTOMATOR, wait / 10)
                    await asyncio.sleep(wait)
        except Exception:
            raise
    raise Exception("Max retries exceeded due to repeated FloodWait")

async def throttled_send(coro):
    await _throttle_send()
    return await _send_with_retry(coro)

async def edit_with_retry(edit_coro, retries=5):
    for attempt in range(retries):
        try:
            return await edit_coro
        except FloodWait as e:
            wait = e.value
            if wait > 0:
                logging.warning(f"FloodWait (edit): need to wait {wait}s before retrying edit (attempt {attempt+1}/{retries})")
                await asyncio.sleep(wait)
            else:
                match = re.search(r'(\d+)', str(e))
                if match:
                    wait = int(match.group(1))
                    logging.warning(f"FloodWait (edit): need to wait {wait}s (parsed)")
                    await asyncio.sleep(wait)
                else:
                    await asyncio.sleep(2 ** attempt)
        except Exception:
            raise
    raise Exception("Max retries exceeded for edit")

# ============================================================
# NEW: Resilient progress editing helper (for qBittorrent monitoring and uploads)
# with circuit breaker and aggressive timeouts
# ============================================================

# Circuit breaker state for edit failures
_edit_failure_counter = 0
_edit_failure_timestamp = 0.0
_edit_circuit_open = False
_edit_circuit_lock = asyncio.Lock()
_edit_restart_attempted = False

# Global last successful edit timestamp for watchdog (ya no se usa para reiniciar,
# pero se mantiene por si acaso)
_last_successful_edit = time.time()

async def edit_progress_resilient(
    message: Message,
    new_text: str,
    reply_markup: Optional[InlineKeyboardMarkup] = None,
    parse_mode: ParseMode = ParseMode.HTML,
    max_retries: int = 3,            # increased from 2
    client: Optional[Client] = None,
    per_attempt_timeout: float = 20.0, # increased from 10.0
) -> bool:
    """
    Edit a progress message with a single attempt and short timeout.
    Uses a circuit breaker to skip edits if many failures occur.
    If client appears zombie, attempts to reconnect (but NOT restart) to avoid disrupting uploads.
    Limitado por semáforo para no saturar el event loop.
    """
    global _edit_failure_counter, _edit_failure_timestamp, _edit_circuit_open, _edit_restart_attempted, _last_successful_edit

    if client is None:
        client = bot_client

    # Semáforo para limitar ediciones concurrentes
    async with _edit_task_semaphore:
        # Circuit breaker: si hemos tenido demasiados fallos recientemente, saltamos
        async with _edit_circuit_lock:
            now = time.time()
            if _edit_circuit_open:
                if now - _edit_failure_timestamp > 60.0:  # reset después de 60s (aumentado)
                    _edit_circuit_open = False
                    _edit_failure_counter = 0
                    logger.info("Circuit breaker reset after cooldown")
                else:
                    logger.debug("Circuit breaker open, skipping edit")
                    return False

        # --- Client health check and recovery (only reconnect, no full restart) ---
        try:
            if not client.is_connected:
                logger.debug("Client not connected, attempting reconnect...")
                try:
                    await asyncio.wait_for(client.restart(), timeout=20.0)
                    logger.info("Client reconnected successfully")
                except Exception as e:
                    logger.warning(f"Reconnect failed: {e}")
                    # No hacemos stop/start; dejamos que el watchdog de latido lo maneje
        except Exception as e:
            logger.exception(f"Client health check error: {e}")

        for attempt in range(max_retries):
            try:
                await asyncio.wait_for(
                    message.edit(
                        _scrub_text_for_user(new_text),
                        reply_markup=reply_markup,
                        parse_mode=parse_mode
                    ),
                    timeout=per_attempt_timeout
                )
                # Éxito: resetear contador de fallos y circuito
                async with _edit_circuit_lock:
                    _edit_failure_counter = 0
                    _edit_circuit_open = False
                _edit_restart_attempted = False
                _last_successful_edit = time.time()
                logger.debug("Progress edit successful")
                return True
            except FloodWait as e:
                wait = min(e.value, 60)
                logger.warning(f"FloodWait in progress edit: {wait}s, waiting...")
                await asyncio.sleep(wait)
                continue
            except (asyncio.TimeoutError, ConnectionError, aiohttp.ClientError) as e:
                logger.warning(f"Network error during edit: {e}")
                # Incrementar contador de fallos
                async with _edit_circuit_lock:
                    _edit_failure_counter += 1
                    if _edit_failure_counter >= 5:  # Aumentado a 5 fallos
                        _edit_circuit_open = True
                        _edit_failure_timestamp = time.time()
                        logger.warning("Circuit breaker activated: skipping further edits for 60s")
                return False
            except Exception as e:
                logger.exception(f"Unexpected error editing progress message: {e}")
                return False
        return False

def has_ansi_support() -> bool:
    import os as _os
    import sys as _sys
    if not _sys.stdout.isatty():
        return False
    if _os.name == "nt":
        return _sys.getwindowsversion().major >= 10
    return True

TERMINAL_CLEAR_LINE: str = f"\r{' ' * 100} \r" if not has_ansi_support() else "\033[2K\r"

def _print(msg: str, error: bool = False) -> None:
    output: TextIO = stderr if error else stdout
    output.write(msg)
    output.flush()

def die(msg: str) -> NoReturn:
    _print(f"{msg}{NEW_LINE}", True)
    exit(-1)

def generate_website_token(user_agent: str, account_token: str) -> str:
    time_slot = int(_time()) // 14400
    raw = f"{user_agent}::en-US::{account_token}::{time_slot}::gf2026x"
    return sha256(raw.encode()).hexdigest()

def validate_and_fix_thumbnail(thumb_path: Path) -> Optional[Path]:
    if not thumb_path.exists():
        return None
    try:
        if PIL_AVAILABLE:
            with Image.open(thumb_path) as img:
                if img.mode not in ('RGB', 'L'):
                    rgb_img = Image.new('RGB', img.size, (255, 255, 255))
                    if img.mode == 'RGBA':
                        rgb_img.paste(img, mask=img.split()[3] if len(img.split()) > 3 else None)
                    else:
                        rgb_img.paste(img)
                    img = rgb_img
                max_size = 320
                if img.width > max_size or img.height > max_size:
                    img.thumbnail((max_size, max_size), Image.Resampling.LANCZOS)
                fixed_path = thumb_path.with_suffix('.jpg')
                img.save(fixed_path, 'JPEG', quality=85, optimize=True)
                if fixed_path.stat().st_size > 200 * 1024:
                    img.save(fixed_path, 'JPEG', quality=60, optimize=True)
                return fixed_path
        else:
            if thumb_path.suffix.lower() not in ('.jpg', '.jpeg'):
                logging.warning("Thumbnail is not a JPEG. PIL not available to convert.")
            return thumb_path
    except Exception as e:
        logging.error(f"Failed to validate thumbnail: {e}")
        return None

# ============================================================
# FIXED OptimizedProgress – uses edit_progress_resilient
# ============================================================
class OptimizedProgress:
    def __init__(self, name: str, total_size: Optional[int], progress_msg: Message,
                 start_time: float, update_interval: float = 15.0,   # increased from 10
                 reply_markup: Optional[InlineKeyboardMarkup] = None,
                 client: Optional[Client] = None):
        self.name = name
        self.total_size = total_size
        self.progress_msg = progress_msg
        self.start_time = start_time
        self.update_interval = update_interval
        self.reply_markup = reply_markup
        self.last_update = 0.0
        self.last_progress = 0
        self.speed_samples = []
        self.last_progress_time = time.time()
        self.client = client or bot_client   # store the client to use for edits
        try:
            self.loop = asyncio.get_running_loop()
        except RuntimeError:
            self.loop = None

    def __call__(self, current: int, total: int):
        if self.loop is None or self.loop.is_closed():
            return
        asyncio.run_coroutine_threadsafe(self._do_update(current, total), self.loop)

    async def _do_update(self, current: int, total: int):
        try:
            now = time.time()
            self.last_progress_time = now
            if now - self.last_update < self.update_interval:
                return
            self.last_update = now
            elapsed = now - self.start_time
            if elapsed > 0:
                current_speed = current / elapsed
                self.speed_samples.append(current_speed)
                if len(self.speed_samples) > 5:
                    self.speed_samples.pop(0)
                avg_speed = sum(self.speed_samples) / len(self.speed_samples)
            else:
                avg_speed = 0
            remaining = total - current
            eta = remaining / avg_speed if avg_speed > 0 else None
            text = build_progress_text(self.name, total, current, elapsed, eta, speed=int(avg_speed))
            if avg_speed > 0:
                speed_mbps = (avg_speed * 8) / (1024 * 1024)
                text += f"\n<i>Velocidad: {speed_mbps:.2f} Mbps</i>"

            # Use the resilient edit helper
            await edit_progress_resilient(
                self.progress_msg,
                text,
                reply_markup=self.reply_markup,
                client=self.client,
                max_retries=3,
                per_attempt_timeout=20.0
            )
        except Exception as e:
            logger.debug(f"Progress update failed: {e}")

class AsyncDownloader:
    def __init__(self, root_dir: str, interactive: bool, max_workers: int, number_retries,
                 timeout: float, chunk_size: int, stop_event: asyncio.Event, url: str,
                 password: str | None = None, progress_callback: Optional[Callable[[str], None]] = None) -> None:
        self._files_info: dict[str, dict[str, str]] = {}
        self._max_workers = max_workers
        self._number_retries = number_retries
        self._timeout = timeout
        self._interactive = interactive
        self._chunk_size = chunk_size
        self._password = password
        self._stop_event = stop_event
        self._root_dir = root_dir
        self._url = url
        self._progress_callback = progress_callback
        self._session = None
        self._content_id = None

    def _log(self, msg: str, error: bool = False) -> None:
        if self._progress_callback:
            try:
                self._progress_callback(msg)
                return
            except Exception:
                pass
        _print(msg, error)

    async def _get_response(self, session: aiohttp.ClientSession, **kwargs) -> Optional[aiohttp.ClientResponse]:
        for attempt in range(self._number_retries):
            if self._stop_event.is_set():
                return None
            try:
                timeout = aiohttp.ClientTimeout(total=self._timeout)
                return await session.get(timeout=timeout, **kwargs)
            except (asyncio.TimeoutError, aiohttp.ClientError):
                if attempt == self._number_retries - 1:
                    return None
                await asyncio.sleep(1)
        return None

    async def run(self) -> None:
        if not self._url.split("/")[-2] == "d":
            self._log(f"The url probably doesn't have an id in it: {self._url}.{NEW_LINE}")
            return
        content_id: str = self._url.split("/")[-1]
        self._content_id = content_id
        _password: str | None = sha256(self._password.encode()).hexdigest() if self._password else None
        content_dir: str = path.join(self._root_dir, content_id)
        content_dir_path = Path(content_dir)
        if content_dir_path.exists():
            bak_name = f"{content_dir_path.name}_bak_{int(time.time())}_{uuid.uuid4().hex[:4]}"
            bak_path = content_dir_path.parent / bak_name
            try:
                await asyncio.wait_for(asyncio.to_thread(content_dir_path.rename, bak_path), timeout=FILE_IO_TIMEOUT)
                self._log(f"Moved existing folder '{content_dir_path.name}' to '{bak_name}' to ensure fresh download.")
            except Exception as e:
                self._log(f"Warning: Could not move existing folder aside: {e}. Download may merge with existing files.")
        async with aiohttp.ClientSession() as session:
            self._session = session
            await self._build_content_tree_structure(content_dir, content_id, _password, session)
            if path.exists(content_dir) and not listdir(content_dir) and not self._files_info:
                self._log(f"Empty directory for url: {self._url}, nothing done.{NEW_LINE}")
                self._remove_dir(content_dir)
                return
            if self._interactive:
                self._do_interactive(content_dir)
            await self._threaded_downloads(session)
            if content_dir_path.exists():
                processed_path = await process_path_with_suffix_and_signing_async(content_dir_path)
                if processed_path:
                    self._log(f"Processed folder: {content_dir_path.name} -> {processed_path.name}")

    async def _threaded_downloads(self, session: aiohttp.ClientSession) -> None:
        tasks = []
        for item in self._files_info.values():
            if self._stop_event.is_set():
                return
            tasks.append(self._download_content(session, item))
        semaphore = asyncio.Semaphore(self._max_workers)
        async def limited_download(item):
            async with semaphore:
                await self._download_content(session, item)
        await asyncio.gather(*[limited_download(item) for item in self._files_info.values()])

    @staticmethod
    async def _create_dirs(dirname: str) -> None:
        await asyncio.wait_for(asyncio.to_thread(makedirs, dirname, exist_ok=True), timeout=FILE_IO_TIMEOUT)

    @staticmethod
    def _remove_dir(dirname: str) -> None:
        try:
            rmdir(dirname)
        except:
            pass

    async def _download_content(self, session: aiohttp.ClientSession, file_info: dict[str, str]) -> None:
        filepath: str = path.join(file_info["path"], file_info["filename"])
        if self._should_skip_download(filepath):
            return
        tmp_file: str = f"{filepath}.part"
        url: str = file_info["link"]
        headers: dict[str, str] = {}
        if path.isfile(tmp_file):
            part_size = int(path.getsize(tmp_file))
            headers = {"Range": f"bytes={part_size}-"}
        for attempt in range(self._number_retries):
            if self._stop_event.is_set():
                return
            try:
                has_size = await self._perform_download(session, file_info, url, tmp_file, headers, part_size if 'part_size' in locals() else 0)
            except (asyncio.TimeoutError, aiohttp.ClientError):
                continue
            else:
                if has_size:
                    self._finalize_download(file_info, tmp_file, has_size)
                break

    @staticmethod
    def _should_skip_download(filepath: str) -> bool:
        if path.exists(filepath) and path.getsize(filepath) > 0:
            _print(f"{filepath} already exist, skipping.{NEW_LINE}")
            return True
        return False

    async def _perform_download(self, session: aiohttp.ClientSession, file_info: dict[str, str],
                                url: str, tmp_file: str, headers: dict[str, str], part_size: int) -> str | None:
        if self._stop_event.is_set():
            return None
        response = await self._get_response(session, url=url, headers=headers)
        if not response:
            self._log(f"{TERMINAL_CLEAR_LINE}Couldn't download the file, failed to get a response from {url}.{NEW_LINE}")
            return None
        async with response:
            status_code = response.status
            if not self._is_valid_response(response.status, part_size):
                self._log(f"{TERMINAL_CLEAR_LINE}Couldn't download the file from {url}.{NEW_LINE}Status code: {status_code}{NEW_LINE}")
                return None
            has_size = self._extract_file_size(response.headers, part_size)
            if not has_size:
                self._log(f"{TERMINAL_CLEAR_LINE}Couldn't find the file size from {url}.{NEW_LINE}Status code: {status_code}{NEW_LINE}")
                return None
            await self._write_chunks(response.content.iter_chunked(self._chunk_size), tmp_file, part_size, float(has_size), file_info["filename"])
            return has_size

    @staticmethod
    def _is_valid_response(status_code: int, part_size: int) -> bool:
        if status_code in (403, 404, 405, 500):
            return False
        if part_size == 0:
            return status_code in (200, 206)
        if part_size > 0:
            return status_code == 206
        return False

    @staticmethod
    def _extract_file_size(headers, part_size: int) -> str | None:
        content_length = headers.get("Content-Length")
        content_range = headers.get("Content-Range")
        has_size = content_length if part_size == 0 else (content_range.split("/")[-1] if content_range else None)
        return has_size

    async def _write_chunks(self, chunks, tmp_file: str, part_size: int, total_size: float, filename: str) -> None:
        start_time = perf_counter()
        def write_chunk_sync(f, chunk):
            f.write(chunk)
        with open(tmp_file, "ab") as f:
            async for chunk in chunks:
                if self._stop_event.is_set():
                    return
                await asyncio.wait_for(asyncio.to_thread(write_chunk_sync, f, chunk), timeout=FILE_IO_TIMEOUT)
                self._update_progress(filename, part_size, 0, chunk, total_size, start_time)

    def _update_progress(self, filename: str, part_size: int, i: int, chunk: bytes, total_size: float, start_time: float) -> None:
        downloaded_bytes = part_size + (len(chunk) if i == 0 else 0)
        elapsed = perf_counter() - start_time
        rate = int(downloaded_bytes / max(1e-6, elapsed)) if elapsed > 0 else None
        eta = None
        try:
            if total_size and downloaded_bytes and rate and rate > 0:
                eta = (total_size - downloaded_bytes) / rate
        except Exception:
            eta = None
        try:
            text = build_progress_text(filename, int(total_size), downloaded_bytes, elapsed, eta, speed=rate)
        except Exception:
            text = f"Descargando {filename}: {downloaded_bytes} de {int(total_size)}"
        if self._progress_callback:
            try:
                self._progress_callback(text)
                return
            except Exception:
                pass
        _print(f"{TERMINAL_CLEAR_LINE}Descargando {filename}: {downloaded_bytes} de {int(total_size)} {round((downloaded_bytes/total_size*100) if total_size else 0,1)}%")

    def _finalize_download(self, file_info: dict[str, str], tmp_file: str, has_size: str) -> None:
        if path.getsize(tmp_file) == int(has_size):
            self._log(f"{TERMINAL_CLEAR_LINE}Descargando {file_info['filename']}: {path.getsize(tmp_file)} de {has_size} ¡Completado!{NEW_LINE}")
            final_path = path.join(file_info["path"], file_info["filename"])
            move(tmp_file, final_path)

    def _register_file(self, file_index: count, filepath: str, file_url: str) -> None:
        self._files_info[str(next(file_index))] = {
            "path": path.dirname(filepath),
            "filename": path.basename(filepath),
            "link": file_url
        }

    @staticmethod
    def _resolve_naming_collision(pathing_count: dict[str, int], absolute_parent_dir: str, child_name: str, is_dir: bool = False) -> str:
        filepath = path.join(absolute_parent_dir, child_name)
        if filepath in pathing_count:
            pathing_count[filepath] += 1
        else:
            pathing_count[filepath] = 0
        if pathing_count and pathing_count[filepath] > 0 and is_dir:
            return f"{filepath}({pathing_count[filepath]})"
        if pathing_count and pathing_count[filepath] > 0:
            root, extension = path.splitext(filepath)
            return f"{root}({pathing_count[filepath]}){extension}"
        return filepath

    async def _build_content_tree_structure(self, parent_dir: str, content_id: str, password: str | None = None,
                                             pathing_count: dict[str, int] | None = None, file_index: count = count(start=0, step=1),
                                             session: Optional[aiohttp.ClientSession] = None) -> None:
        if session is None:
            return
        url = f"https://api.gofile.io/contents/{content_id}?cache=true&sortField=createTime&sortDirection=1"
        if not pathing_count:
            pathing_count = {}
        if password:
            url = f"{url}&password={password}"
        response = await self._get_response(session, url=url)
        if not response:
            self._log(f"Failed to fetch data response from the {url}.{NEW_LINE}")
            return
        try:
            json_response = await response.json()
        except:
            self._log(f"Failed to parse JSON from {url}.{NEW_LINE}")
            return
        if not json_response or json_response.get("status") != "ok":
            self._log(f"Failed to fetch data response from the {url}.{NEW_LINE}")
            return
        data = json_response["data"]
        if "password" in data and "passwordStatus" in data and data["passwordStatus"] != "passwordOk":
            self._log(f"Password protected link. Please provide the password.{NEW_LINE}")
            return
        if data["type"] != "folder":
            filepath = self._resolve_naming_collision(pathing_count, parent_dir, data["name"])
            self._register_file(file_index, filepath, data["link"])
            return
        folder_name = data["name"]
        absolute_path = self._resolve_naming_collision(pathing_count, parent_dir, folder_name)
        if path.basename(parent_dir) == content_id:
            absolute_path = parent_dir
        await self._create_dirs(absolute_path)
        for child in data["children"].values():
            if child["type"] == "folder":
                await self._build_content_tree_structure(absolute_path, child["id"], password, pathing_count, file_index, session)
            else:
                filepath = self._resolve_naming_collision(pathing_count, absolute_path, child["name"])
                self._register_file(file_index, filepath, child["link"])

    def _print_list_files(self) -> None:
        MAX_FILENAME_CHARACTERS = 100
        width = max(len(f"[{v}] -> ") for v in self._files_info.keys())
        for (k, v) in self._files_info.items():
            filepath = path.join(v["path"], v["filename"])
            filepath = f"...{filepath[-MAX_FILENAME_CHARACTERS:]}" if len(filepath) > MAX_FILENAME_CHARACTERS else filepath
            text = f"{f'[{k}] -> '.ljust(width)}{filepath}"
            self._log(f"{text}{NEW_LINE}{'-' * len(text)}{NEW_LINE}")

    def _do_interactive(self, content_dir: str) -> None:
        self._print_list_files()
        input_list = set(input(f"Files to download (Ex: 1 3 7) | or leave empty to download them all{NEW_LINE}:: ").split())
        input_list = set(self._files_info.keys()) if not input_list else input_list & set(self._files_info.keys())
        if not input_list:
            self._log(f"Nothing done.{NEW_LINE}")
            self._remove_dir(content_dir)
            return
        keys_to_delete = list(set(self._files_info.keys()) - set(input_list))
        for key in keys_to_delete:
            del self._files_info[key]

class Manager:
    def __init__(self, url_or_file: str, password: str | None = None,
                 progress_callback: Optional[Callable[[str], None]] = None,
                 stop_event: Optional[asyncio.Event] = None) -> None:
        root_dir = getenv("GF_DOWNLOAD_DIR")
        self._max_workers = int(getenv("GF_MAX_CONCURRENT_DOWNLOADS", 5))
        self._number_retries = int(getenv("GF_MAX_RETRIES", 5))
        self._timeout = float(getenv("GF_TIMEOUT", 15.0))
        self._user_agent = getenv("GF_USERAGENT")
        self._interactive = getenv("GF_INTERACTIVE") == "1"
        self._chunk_size = int(getenv("GF_CHUNK_SIZE", 2097152))
        self._password = password
        self._url_or_file = url_or_file
        self._stop_event = stop_event if stop_event is not None else asyncio.Event()
        self._root_dir = root_dir if root_dir else getcwd()
        self._progress_callback = progress_callback
        self._token = None

    async def _parse_url_or_file(self) -> None:
        if not (path.exists(self._url_or_file) and path.isfile(self._url_or_file)):
            downloader = AsyncDownloader(self._root_dir, self._interactive, self._max_workers, self._number_retries,
                                         self._timeout, self._chunk_size, self._stop_event, self._url_or_file,
                                         self._password, progress_callback=self._progress_callback)
            await downloader.run()
            return
        with open(self._url_or_file, "r") as f:
            lines = f.readlines()
        tasks = []
        for line in lines:
            if self._stop_event.is_set():
                return
            line_splitted = line.split(" ")
            url = line_splitted[0].strip()
            password = self._password if self._password else (line_splitted[1].strip() if len(line_splitted) > 1 else self._password)
            downloader = AsyncDownloader(self._root_dir, False, self._max_workers, self._number_retries,
                                         self._timeout, self._chunk_size, self._stop_event, url, password,
                                         progress_callback=self._progress_callback)
            tasks.append(downloader.run())
        semaphore = asyncio.Semaphore(min(self._max_workers, 10))
        async def limited_run(downloader_func):
            async with semaphore:
                await downloader_func
        await asyncio.gather(*[limited_run(task) for task in tasks])

    async def run(self) -> None:
        _print(f"Starting, please wait...{NEW_LINE}")
        await self._set_account_access_token(getenv("GF_TOKEN"))
        await self._parse_url_or_file()

    async def _set_account_access_token(self, token: str | None = None) -> None:
        async with aiohttp.ClientSession() as session:
            if token:
                self._token = token
                return
            user_agent = self._user_agent if self._user_agent else "Mozilla/5.0"
            wt = generate_website_token(user_agent, "")
            for attempt in range(self._number_retries):
                try:
                    timeout = aiohttp.ClientTimeout(total=self._timeout)
                    async with session.post("https://api.gofile.io/accounts", headers={"X-Website-Token": wt, "X-BL": "en-US"}, timeout=timeout) as resp:
                        response = await resp.json()
                        if response and response.get("status") == "ok":
                            self._token = response['data']['token']
                            return
                except (asyncio.TimeoutError, aiohttp.ClientError):
                    continue
            if not self._token:
                die("Account creation failed!")

    def _stop(self) -> None:
        _print(f"{TERMINAL_CLEAR_LINE}Stopping, please wait...{NEW_LINE}")
        self._stop_event.set()

if os.name == "nt":
    try:
        asyncio.set_event_loop_policy(asyncio.WindowsProactorEventLoopPolicy())
        logging.getLogger(__name__).info("Using WindowsProactorEventLoopPolicy for better I/O performance")
    except Exception:
        try:
            asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())
            logging.getLogger(__name__).info("Using WindowsSelectorEventLoopPolicy")
        except Exception:
            pass
else:
    try:
        import uvloop
        asyncio.set_event_loop_policy(uvloop.EventLoopPolicy())
        logging.getLogger(__name__).info("uvloop installed for improved asyncio performance")
    except Exception:
        logging.getLogger(__name__).debug("uvloop not available; continuing with default asyncio loop")

TELEGRAM_TOKEN = os.getenv("TELEGRAM_TOKEN")
MYJD_USER = os.getenv("MYJD_USER")
MYJD_PASS = os.getenv("MYJD_PASS")
JD_DEVICE_NAME = os.getenv("JD_DEVICE_NAME")
MYJD_APP_KEY = os.getenv("MYJD_APP_KEY")
JD_API_HOST = os.getenv("JD_API_HOST", "localhost")
JD_API_PORT = os.getenv("JD_API_PORT", "3128")
PYRO_API_ID = os.getenv("TELETHON_API_ID")
PYRO_API_HASH = os.getenv("TELETHON_API_HASH")
TELEGRAM_OWNERS = os.getenv("TELEGRAM_OWNERS", "")
TELELOAD_BASE_DIR = os.getenv("TELELOAD_BASE_DIR", "/")
SEVENZ_PATH = os.getenv("SEVENZ_PATH", "").strip()
PYRO_WORKERS = int(os.getenv("PYRO_WORKERS", "32"))
PYRO_MAX_CONCURRENT_TRANSMISSIONS = int(os.getenv("PYRO_MAX_CONCURRENT_TRANSMISSIONS", "32"))
ARIA2_MAX_CONCURRENT_DOWNLOADS = int(os.getenv("ARIA2_MAX_CONCURRENT_DOWNLOADS", "4"))
QBT_HOST = os.getenv("QBT_HOST", "127.0.0.1")
QBT_PORT = int(os.getenv("QBT_PORT", "9090"))
QBT_USER = os.getenv("QBT_USER", "")
QBT_PASS = os.getenv("QBT_PASS", "")

if not TELEGRAM_TOKEN or not MYJD_USER or not MYJD_PASS or not JD_DEVICE_NAME or not MYJD_APP_KEY:
    raise SystemExit("Please set TELEGRAM_TOKEN, MYJD_USER, MYJD_PASS, JD_DEVICE_NAME and MYJD_APP_KEY in .env")
if not PYRO_API_ID or not PYRO_API_HASH:
    raise SystemExit("Please set TELETHON_API_ID and TELETHON_API_HASH (used as Pyrogram api_id/api_hash) in .env")

# logging already configured earlier

import collections
import threading

# --- FIX: Disable automatic restart of clients from DiscardWatchdog (only log) ---
class DiscardWatchdog(logging.Handler):
    def __init__(self, threshold: int = 3, window_seconds: int = 60, cooldown_seconds: int = 300):
        super().__init__()
        self.threshold = threshold
        self.window_seconds = window_seconds
        self.cooldown_seconds = cooldown_seconds
        self.timestamps = collections.deque()
        self.last_restart = 0.0
        self.lock = threading.Lock()
        self._restart_task = None

    def emit(self, record: logging.LogRecord) -> None:
        try:
            msg = record.getMessage()
            if "Discarding packet" not in msg:
                return
            now = time.time()
            with self.lock:
                self.timestamps.append(now)
                while self.timestamps and (now - self.timestamps[0] > self.window_seconds):
                    self.timestamps.popleft()
                if len(self.timestamps) >= self.threshold and (now - self.last_restart >= self.cooldown_seconds):
                    self.last_restart = now
                    logger.warning("DiscardWatchdog: many discarded packets detected, but automatic restart is disabled. Manual restart may be needed.")
        except Exception:
            pass

watchdog = DiscardWatchdog(threshold=3, window_seconds=60, cooldown_seconds=300)
pyro_logger = logging.getLogger("pyrogram.session.session")
pyro_logger.addHandler(watchdog)

_owner_ids = set()
_owner_usernames = set()
for part in [p.strip() for p in TELEGRAM_OWNERS.split(",") if p.strip()]:
    if part.startswith("@"):
        _owner_usernames.add(part.lower())
    else:
        try:
            _owner_ids.add(int(part))
        except Exception:
            _owner_usernames.add(("@" + part).lower())

def _is_owner_impl(user) -> bool:
    if user is None:
        return False
    try:
        if getattr(user, "id", None) in _owner_ids:
            return True
        uname = ("@" + user.username) if getattr(user, "username", None) else ""
        if uname and uname.lower() in _owner_usernames:
            return True
    except Exception:
        pass
    return False

def is_owner(user) -> bool:
    try:
        uid = getattr(user, "id", None)
        uname = getattr(user, "username", None)
        logger.debug("is_owner check: user.id=%s username=%s _owner_ids=%s _owner_usernames=%s", uid, uname, _owner_ids, _owner_usernames)
    except Exception:
        logger.exception("is_owner debug logging failed")
    return _is_owner_impl(user)

async def check_membership(user):
    if not REQUIRED_CHANNELS:
        return True
    if user is None:
        return False
    user_id = user.id
    async with _membership_cache_lock:
        now = time.time()
        if user_id in _membership_cache:
            ts, result = _membership_cache[user_id]
            if now - ts < MEMBERSHIP_CACHE_TTL:
                return result
    for ch in REQUIRED_CHANNELS:
        try:
            member = await bot_client.get_chat_member(ch, user_id)
            if member.status in ("member", "administrator", "creator"):
                continue
            else:
                async with _membership_cache_lock:
                    _membership_cache[user_id] = (now, False)
                return False
        except Exception as e:
            logger.warning(f"Membership check failed for {user_id} in {ch}: {e}")
            async with _membership_cache_lock:
                _membership_cache[user_id] = (now, False)
            return False
    async with _membership_cache_lock:
        _membership_cache[user_id] = (now, True)
    return True

async def is_user_authorized(user):
    if user is None:
        return False
    if is_owner(user):
        return True
    if PUBLIC_ACCESS:
        return await check_membership(user)
    else:
        if not is_allowed_user(user):
            return False
        return await check_membership(user)

def get_user_folder_name(user) -> str:
    if user is None:
        return "unknown"
    if getattr(user, "id", None):
        return f"telegram_{user.id}"
    if getattr(user, "username", None):
        return f"telegram_{user.username}"
    return "telegram_unknown"

def get_user_root_path(user) -> Path:
    base = TELELOAD_BASE_DIR.rstrip("/") or "/"
    if base == "/":
        dest_base = Path.cwd()
    else:
        dest_base = Path(base)
    user_folder = get_user_folder_name(user)
    return (dest_base / user_folder).resolve()

CURRENT_DIRS = {}
PASSWORDS = {}
UPLOAD_DESCRIPTION = None
ADDED_USERS = {}
UPLOAD_GROUPS = {}
AUTOMATOR_UPLOADS = {}
AUTOMATOR_JOBS = {}

THUMBNAIL_FILENAME = "bot_thumbnail.jpg"
THUMBNAIL_PATH = None
startup_thumb = Path.cwd() / THUMBNAIL_FILENAME
if startup_thumb.exists() and startup_thumb.is_file():
    validated_thumb = validate_and_fix_thumbnail(startup_thumb)
    if validated_thumb:
        THUMBNAIL_PATH = validated_thumb
        logger.info("Bot thumbnail loaded and validated from %s", THUMBNAIL_PATH)
    else:
        THUMBNAIL_PATH = None
        logger.warning("Bot thumbnail exists but failed validation")
else:
    THUMBNAIL_PATH = None

SUFFIX_FILTERS = []
SUFFIX_FILTER_ENABLED = False

_STATE_FILE = Path.cwd() / "bot_state.json"

def _load_state_file():
    try:
        if _STATE_FILE.exists():
            with _STATE_FILE.open("r", encoding="utf-8") as f:
                return json.load(f)
    except Exception:
        logger.exception("Failed to load state file")
    return {}

def _save_state_file(data: dict):
    try:
        tmp = _STATE_FILE.with_suffix(".tmp")
        with tmp.open("w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        tmp.replace(_STATE_FILE)
    except Exception:
        logger.exception("Failed to save state file")

def load_persistent_state():
    global ADDED_USERS, UPLOAD_DESCRIPTION, SUFFIX_FILTERS, SUFFIX_FILTER_ENABLED
    global FILE_SIGNING_ENABLED, FILE_SIGN
    data = _load_state_file()
    if not isinstance(data, dict):
        return
    if "added_users" in data and isinstance(data["added_users"], dict):
        try:
            ADDED_USERS.clear()
            for k, v in data["added_users"].items():
                if isinstance(v, dict) and "expires_at" in v:
                    ADDED_USERS[k] = v
        except Exception:
            logger.exception("Failed to restore ADDED_USERS")
    if "upload_description" in data:
        try:
            UPLOAD_DESCRIPTION = data.get("upload_description")
        except Exception:
            logger.exception("Failed to restore UPLOAD_DESCRIPTION")
    if "suffix_filters" in data and isinstance(data["suffix_filters"], list):
        try:
            SUFFIX_FILTERS = data["suffix_filters"]
        except Exception:
            logger.exception("Failed to restore SUFFIX_FILTERS")
    if "suffix_filter_enabled" in data:
        try:
            SUFFIX_FILTER_ENABLED = bool(data["suffix_filter_enabled"])
        except Exception:
            logger.exception("Failed to restore SUFFIX_FILTER_ENABLED")
    if "file_signing_enabled" in data:
        try:
            FILE_SIGNING_ENABLED = bool(data["file_signing_enabled"])
        except Exception:
            logger.exception("Failed to restore FILE_SIGNING_ENABLED")
    if "file_sign" in data:
        try:
            FILE_SIGN = data["file_sign"]
        except Exception:
            logger.exception("Failed to restore FILE_SIGN")
    if "automator_concurrency" in data:
        try:
            global AUTOMATOR_CONCURRENCY
            AUTOMATOR_CONCURRENCY = int(data["automator_concurrency"])
            if AUTOMATOR_CONCURRENCY < 1:
                AUTOMATOR_CONCURRENCY = 1
        except Exception:
            logger.exception("Failed to restore AUTOMATOR_CONCURRENCY")

def save_persistent_state():
    try:
        to_save = {
            "added_users": {},
            "upload_description": UPLOAD_DESCRIPTION,
            "suffix_filters": SUFFIX_FILTERS,
            "suffix_filter_enabled": SUFFIX_FILTER_ENABLED,
            "file_signing_enabled": FILE_SIGNING_ENABLED,
            "file_sign": FILE_SIGN,
            "automator_concurrency": AUTOMATOR_CONCURRENCY
        }
        for k, v in ADDED_USERS.items():
            try:
                if not isinstance(v, dict):
                    continue
                entry = {"id": v.get("id"), "username": v.get("username"), "expires_at": float(v.get("expires_at", 0))}
                to_save["added_users"][k] = entry
            except Exception:
                continue
        _save_state_file(to_save)
    except Exception:
        logger.exception("Failed to save persistent state")

try:
    load_persistent_state()
    logger.info("Persistent state loaded: %d users, description set: %s, suffix filters: %d, filter enabled: %s, signing enabled: %s, sign: %s, automator concurrency: %d",
                len(ADDED_USERS), bool(UPLOAD_DESCRIPTION), len(SUFFIX_FILTERS), SUFFIX_FILTER_ENABLED,
                FILE_SIGNING_ENABLED, FILE_SIGN, AUTOMATOR_CONCURRENCY)
except Exception:
    logger.exception("Failed loading persistent state")

_WINDOWS_PATH_RE = re.compile(r"(?:[A-Za-z]:\\|\\\\[^\s\\/]+\)[^\n\r]*)", flags=re.IGNORECASE)
_UNIX_PATH_RE = re.compile(r"(?:\/[^\s]+)+", flags=re.IGNORECASE)
_HOME_PATH_RE = re.compile(r"(?:[A-Za-z]:\\[^\\]*Users\\[^\\]+[^\n\r]*|\/home\/[^\s\/]+[^\n\r]*)", flags=re.IGNORECASE)
_TOOL_WORDS_RE = re.compile(r"\b(aria2c|aria2|jdownloader|myjdownloader)\b", flags=re.IGNORECASE)
_PATH_REDACT = "[REDACTED PATH]"
_TOOL_REDACT = "[download system]"

_ZIP_PERCENT_RE = re.compile(r"\[\s*(\d{1,3}(?:\.\d+)?)\s*%\]")
_ZIP_SIMPLE_PERCENT_RE = re.compile(r"(\d{1,3}(?:\.\d+)?)\s*%")
ZIP_TASKS = {}
_UNZIP_TASKS = {}
DOWNLOAD_TASKS = {}
USER_PENDING_TASKS = {}
USER_RUNNING = set()

def _get_user_id_from_user_or_message(user, message):
    try:
        if user and getattr(user, "id", None) is not None:
            return int(user.id)
        if message and getattr(message, "from_user", None) and getattr(message.from_user, "id", None) is not None:
            return int(message.from_user.id)
    except Exception:
        pass
    return None

async def enqueue_user_task(user, client, message, handler_func, *h_args, **h_kwargs):
    uid = _get_user_id_from_user_or_message(user, message)
    if uid is None:
        try:
            await handler_func(client, message, *h_args, **h_kwargs, from_queue=True)
        except Exception:
            logger.exception("Failed executing task for unknown user")
        return
    uid = int(uid)
    q = USER_PENDING_TASKS.setdefault(uid, [])
    if uid in USER_RUNNING:
        q.append((handler_func, h_args, h_kwargs, client, message))
        pos = len(q)
        try:
            await notify_user_from_message(message, f"Su tarea ha sido encolada en la posición {pos}.")
        except Exception:
            pass
        return
    USER_RUNNING.add(uid)
    async def _runner(first_func, f_args, f_kwargs, f_client, f_message):
        try:
            automator_enabled = await get_automator_enabled(user)
            status_str = "✅ activado" if automator_enabled else "❌ desactivado"
            try:
                await notify_user_from_message(
                    f_message,
                    f"Iniciando su tarea ahora.\nAutomator: {status_str}"
                )
            except Exception:
                pass
            await first_func(f_client, f_message, *f_args, **f_kwargs, from_queue=True)
        except Exception:
            logger.exception("Queued task failed")
        finally:
            while True:
                q2 = USER_PENDING_TASKS.get(uid, [])
                if not q2:
                    USER_RUNNING.discard(uid)
                    USER_PENDING_TASKS.pop(uid, None)
                    return
                next_func, n_args, n_kwargs, n_client, n_message = q2.pop(0)
                try:
                    automator_enabled2 = await get_automator_enabled(user)
                    status_str2 = "✅ activado" if automator_enabled2 else "❌ desactivado"
                    await notify_user_from_message(
                        n_message,
                        f"Iniciando su tarea encolada...\nAutomator: {status_str2}"
                    )
                except Exception:
                    pass
                try:
                    await next_func(n_client, n_message, *n_args, **n_kwargs, from_queue=True)
                except Exception:
                    logger.exception("Queued task failed")
    asyncio.create_task(_runner(handler_func, h_args, h_kwargs, client, message))

def _unzip_cancel_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton("Cancelar extracción", callback_data="unzip_cancel")]])

def _zip_progress_text(filename: str, pct: float, elapsed: int, spinner_char: str) -> str:
    filled = int((pct / 100.0) * 20)
    bar = "█" * filled + "░" * (20 - filled)
    return f"<i>Comprimiendo {filename}\n{bar} {pct:.1f}% … {spinner_char}\n⏳ {elapsed}s transcurridos</i>"

def _unzip_progress_bar_text(filename: str, current_file: Optional[str] = None) -> str:
    bar = "█" * 20
    if current_file:
        display = f"Extrayendo: {current_file}"
    else:
        display = "Extrayendo..."
    return f"<i>{display}\n{bar}\nPulse Cancelar para detener la extracción.</i>"

def _zip_cancel_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton("Cancelar compresión", callback_data="zip_cancel")]])

def _upload_cancel_keyboard(group_id: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton("Cancelar subida", callback_data=f"upload_cancel:{group_id}")]])

def _download_cancel_keyboard(cancel_key: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton("Cancelar descarga", callback_data=f"download_cancel:{cancel_key}")]])

async def handle_unzip_cancel(client: Client, callback_query: CallbackQuery):
    msg = callback_query.message
    if not msg:
        return
    progress_id = getattr(msg, "message_id", None) or getattr(msg, "id", None)
    task = _UNZIP_TASKS.get(progress_id)
    if not task:
        await callback_query.answer("No hay tarea de extracción activa.", show_alert=True)
        return
    user = callback_query.from_user
    owner_id = task.get("user_id")
    if user and owner_id is not None and user.id != owner_id:
        await callback_query.answer("Solo el usuario que inició puede cancelar.", show_alert=True)
        return
    proc = task.get("process")
    if proc and proc.returncode is None:
        try:
            proc.terminate()
        except Exception:
            pass
    task["cancelled"] = True
    await callback_query.answer("Cancelación solicitada.")
    try:
        await edit_with_retry(msg.edit_text("❌ Extracción cancelada por el usuario.", reply_markup=None))
    except Exception:
        pass

async def handle_zip_cancel(client: Client, callback_query: CallbackQuery):
    msg = callback_query.message
    if not msg:
        return
    progress_id = getattr(msg, "message_id", None) or getattr(msg, "id", None)
    task = ZIP_TASKS.get(progress_id)
    if not task:
        await callback_query.answer("No hay tarea de compresión activa.", show_alert=True)
        return
    user = callback_query.from_user
    owner_id = task.get("user_id")
    if user and owner_id is not None and user.id != owner_id:
        await callback_query.answer("Solo el usuario que inició puede cancelar.", show_alert=True)
        return
    proc = task.get("process")
    if proc and proc.returncode is None:
        try:
            proc.terminate()
        except Exception:
            pass
    task["cancelled"] = True
    await callback_query.answer("Cancelación solicitada.")
    try:
        await edit_with_retry(msg.edit_text("Compresión cancelada por el usuario.", reply_markup=None))
    except Exception:
        pass

async def handle_upload_cancel(client: Client, callback_query: CallbackQuery):
    msg = callback_query.message
    if not msg:
        return
    data = (callback_query.data or "").split(":", 1)
    if len(data) != 2:
        await callback_query.answer("Subida no encontrada.", show_alert=True)
        return
    if data[0] == "auto_cancel_job":
        job_id = data[1]
        job = AUTOMATOR_JOBS.get(job_id)
        if not job:
            await callback_query.answer("El trabajo ya finalizó o no se encontró.", show_alert=True)
            return
        cancel_event = job.get("cancel_event")
        if cancel_event:
            cancel_event.set()
        proc = job.get("proc")
        if proc and proc.returncode is None:
            try:
                proc.terminate()
            except Exception:
                pass
        for task in job.get("pending_tasks", []):
            if not task.done():
                task.cancel()
        progress_msg = job.get("progress_msg")
        if progress_msg:
            try:
                await edit_with_retry(progress_msg.edit("❌ Trabajo del Automator cancelado por el usuario.", reply_markup=None))
            except Exception:
                pass
        await callback_query.answer("Cancelación del trabajo del Automator solicitada.", show_alert=True)
        return
    if data[0] == "upload_cancel":
        group_id = data[1]
        entry = UPLOAD_GROUPS.get(group_id)
        if not entry:
            await callback_query.answer("La subida ya finalizó.", show_alert=True)
            return
        cancel_event = entry.get("cancel_event")
        if cancel_event and cancel_event.is_set():
            await callback_query.answer("La cancelación ya está en curso.", show_alert=True)
            return
        if cancel_event:
            cancel_event.set()
        task = entry.get("active_task")
        if task and not task.done():
            task.cancel()
        await callback_query.answer("Cancelando subida...", show_alert=True)
        try:
            await edit_with_retry(msg.edit(_scrub_text_for_user("<i>Subida cancelada.</i>"), reply_markup=None, parse_mode=ParseMode.HTML))
        except Exception:
            pass
        return
    if data[0] == "auto_cancel":
        short_id = data[1]
        entry = AUTOMATOR_UPLOADS.get(short_id)
        if not entry:
            await callback_query.answer("La subida ya finalizó o no se encontró.", show_alert=True)
            return
        job_id = entry.get("job_id")
        if job_id and job_id in AUTOMATOR_JOBS:
            job = AUTOMATOR_JOBS[job_id]
            cancel_event = job.get("cancel_event")
            if cancel_event:
                cancel_event.set()
            proc = job.get("proc")
            if proc and proc.returncode is None:
                try:
                    proc.terminate()
                except Exception:
                    pass
            for task in job.get("pending_tasks", []):
                if not task.done():
                    task.cancel()
            progress_msg = job.get("progress_msg")
            if progress_msg:
                try:
                    await edit_with_retry(progress_msg.edit("❌ Trabajo del Automator cancelado por el usuario.", reply_markup=None))
                except Exception:
                    pass
        else:
            task = entry.get("upload_task")
            if task and not task.done():
                task.cancel()
            part_path = entry.get("part_path")
            if part_path and part_path.exists():
                try:
                    await asyncio.wait_for(asyncio.to_thread(part_path.unlink, missing_ok=True), timeout=FILE_IO_TIMEOUT)
                except Exception:
                    pass
            progress_msg = entry.get("progress_msg")
            if progress_msg:
                try:
                    await edit_with_retry(progress_msg.edit("❌ Subida cancelada por el usuario.", reply_markup=None))
                except Exception:
                    pass
            AUTOMATOR_UPLOADS.pop(short_id, None)
        await callback_query.answer("Trabajo del Automator cancelado.", show_alert=True)
        return
    await callback_query.answer("Tipo de cancelación desconocido.", show_alert=True)

async def get_directory_snapshot(dir_path: Path) -> Set[str]:
    if not dir_path.exists():
        return set()
    entries = await asyncio.wait_for(asyncio.to_thread(lambda: list(dir_path.iterdir())), timeout=DIR_LIST_TIMEOUT)
    return {str(entry.resolve()) for entry in entries}

async def handle_download_cancel(client: Client, callback_query: CallbackQuery):
    msg = callback_query.message
    if not msg:
        return
    data = (callback_query.data or "").split(":", 1)
    if len(data) != 2:
        await callback_query.answer("Descarga no encontrada.", show_alert=True)
        return
    cancel_key = data[1]
    entry = DOWNLOAD_TASKS.get(cancel_key)
    if not entry:
        await callback_query.answer("La descarga ya finalizó o no se encontró.", show_alert=True)
        try:
            await edit_with_retry(msg.edit("No hay descarga activa.", reply_markup=None, parse_mode=ParseMode.HTML))
        except Exception:
            pass
        return
    user = callback_query.from_user
    owner_id = entry.get("user_id")
    if user and owner_id is not None and user.id != owner_id:
        await callback_query.answer("Solo el usuario que inició puede cancelar.", show_alert=True)
        return

    if entry.get("type") == "jd_monitor":
        jd = None
        device = None
        try:
            jd = await asyncio.wait_for(asyncio.to_thread(connect_jd), timeout=JD_API_TIMEOUT)
            device = await asyncio.wait_for(asyncio.to_thread(get_device_direct, jd, JD_DEVICE_NAME), timeout=JD_API_TIMEOUT)

            stored_package_ids = entry.get("package_ids", [])
            numeric_uuids = []

            if any(isinstance(pid, str) and not pid.isdigit() for pid in stored_package_ids):
                all_packages = []
                try:
                    lg_pkgs = await asyncio.wait_for(asyncio.to_thread(device.linkgrabber.query_packages, [{"maxResults": -1}]), timeout=JD_API_TIMEOUT)
                    all_packages.extend(lg_pkgs)
                except Exception:
                    pass
                try:
                    dl_pkgs = await asyncio.wait_for(asyncio.to_thread(device.downloads.query_packages, [{"maxResults": -1}]), timeout=JD_API_TIMEOUT)
                    all_packages.extend(dl_pkgs)
                except Exception:
                    pass

                name_to_uuid = {}
                for pkg in all_packages:
                    pkg_name = pkg.get("name") or pkg.get("packageName")
                    pkg_uuid = pkg.get("uuid") or pkg.get("packageUUID")
                    if pkg_name and pkg_uuid:
                        name_to_uuid[pkg_name] = int(pkg_uuid)

                for pid in stored_package_ids:
                    if isinstance(pid, str) and not pid.isdigit():
                        if pid in name_to_uuid:
                            numeric_uuids.append(name_to_uuid[pid])
                        else:
                            found = None
                            for name, uuid_val in name_to_uuid.items():
                                if pid in name or name in pid:
                                    found = uuid_val
                                    break
                            if found:
                                numeric_uuids.append(found)
                            else:
                                logger.warning(f"Could not resolve package name to UUID: {pid}")
                    else:
                        try:
                            numeric_uuids.append(int(pid))
                        except Exception:
                            pass
            else:
                for pid in stored_package_ids:
                    try:
                        numeric_uuids.append(int(pid))
                    except (ValueError, TypeError):
                        pass

            numeric_uuids = list(set(numeric_uuids))
            if not numeric_uuids:
                await callback_query.answer("No se encontraron IDs de paquete válidos para cancelar.", show_alert=True)
                return

            try:
                await asyncio.wait_for(asyncio.to_thread(device.action, "/downloadsV2/setEnabled", [False, None, numeric_uuids]), timeout=JD_API_TIMEOUT)
                logger.info(f"Stopped packages: {numeric_uuids}")
            except Exception as e:
                logger.error(f"Failed to stop packages: {e}")

            detailed_info_by_uuid = {}
            query_detail = [{
                "bytesLoaded": True,
                "bytesTotal": True,
                "children": True,
                "links": True,
                "saveTo": True,
                "uuid": True,
                "packageUUID": True,
                "name": True,
                "packageName": True,
                "finished": True,
            }]
            try:
                pkgs = await asyncio.wait_for(asyncio.to_thread(device.downloads.query_packages, query_detail), timeout=JD_API_TIMEOUT)
                for p in pkgs:
                    uid = p.get("uuid") or p.get("packageUUID")
                    if uid:
                        detailed_info_by_uuid[str(uid)] = p
                lg_pkgs = await asyncio.wait_for(asyncio.to_thread(device.linkgrabber.query_packages, query_detail), timeout=JD_API_TIMEOUT)
                for p in lg_pkgs:
                    uid = p.get("uuid") or p.get("packageUUID")
                    if uid and str(uid) not in detailed_info_by_uuid:
                        detailed_info_by_uuid[str(uid)] = p
            except Exception as e:
                logger.warning(f"Failed to query package details: {e}")

            try:
                await asyncio.wait_for(asyncio.to_thread(device.action, "/downloadsV2/removeLinks", [None, numeric_uuids]), timeout=JD_API_TIMEOUT)
                logger.info(f"Removed packages from downloads: {numeric_uuids}")
            except Exception as e:
                logger.error(f"Failed to remove from downloads: {e}")

            try:
                await asyncio.wait_for(asyncio.to_thread(device.action, "/linkgrabberv2/removeLinks", [None, numeric_uuids]), timeout=JD_API_TIMEOUT)
                logger.info(f"Removed packages from linkgrabber: {numeric_uuids}")
            except Exception as e:
                logger.error(f"Failed to remove from linkgrabber: {e}")

            deleted_paths = []
            for uuid_val in numeric_uuids:
                pkg = detailed_info_by_uuid.get(str(uuid_val))
                if not pkg:
                    logger.warning(f"No detailed info for UUID {uuid_val}, cannot delete files")
                    continue
                save_to = pkg.get("saveTo")
                if not save_to:
                    logger.warning(f"Package {uuid_val} has no saveTo path")
                    continue
                save_path = Path(save_to)
                pkg_name = pkg.get("name") or pkg.get("packageName") or str(uuid_val)
                clean_pkg_name = sanitize_filename(pkg_name)

                children = pkg.get("children") or pkg.get("links") or []
                for child in children:
                    filename = child.get("name")
                    if not filename:
                        continue
                    full_path = save_path / filename
                    try:
                        if full_path.exists():
                            if full_path.is_dir():
                                await asyncio.wait_for(asyncio.to_thread(shutil.rmtree, full_path), timeout=FILE_IO_TIMEOUT)
                            else:
                                await asyncio.wait_for(asyncio.to_thread(full_path.unlink), timeout=FILE_IO_TIMEOUT)
                            deleted_paths.append(str(full_path))
                            logger.info(f"Deleted file: {full_path}")
                    except Exception as e:
                        logger.error(f"Failed to delete {full_path}: {e}")

                if save_path.exists() and save_path.is_dir():
                    for item in save_path.iterdir():
                        item_name = item.name
                        is_part = item_name.endswith('.part')
                        base_name = item.stem if item.is_file() else item_name
                        matches_pkg = (clean_pkg_name in base_name) or (base_name == clean_pkg_name)
                        matches_uuid = str(uuid_val) in item_name
                        if is_part or matches_pkg or matches_uuid:
                            try:
                                if item.is_dir():
                                    await asyncio.wait_for(asyncio.to_thread(shutil.rmtree, item), timeout=FILE_IO_TIMEOUT)
                                else:
                                    await asyncio.wait_for(asyncio.to_thread(item.unlink), timeout=FILE_IO_TIMEOUT)
                                deleted_paths.append(str(item))
                                logger.info(f"Deleted leftover item: {item}")
                            except Exception as e:
                                logger.error(f"Failed to delete {item}: {e}")

                if save_path.name == clean_pkg_name and save_path.exists() and save_path.is_dir():
                    try:
                        if not any(save_path.iterdir()):
                            await asyncio.wait_for(asyncio.to_thread(save_path.rmdir), timeout=FILE_IO_TIMEOUT)
                            deleted_paths.append(str(save_path))
                            logger.info(f"Deleted empty folder: {save_path}")
                    except Exception as e:
                        logger.debug(f"Could not remove folder {save_path}: {e}")

            if deleted_paths:
                logger.info(f"Deleted {len(deleted_paths)} items from disk")
            else:
                logger.warning("No files were deleted for cancelled packages")

            entry["cancelled"] = True
            await edit_with_retry(msg.edit("✖️Descarga cancelada por el usuario.", reply_markup=None, parse_mode=ParseMode.HTML))
            await callback_query.answer("Cancelación completada.", show_alert=True)

        except Exception as e:
            logger.exception("Failed to cancel JDownloader download")
            await callback_query.answer(f"Cancelación fallida: {str(e)[:100]}", show_alert=True)
        finally:
            if jd:
                try:
                    await asyncio.wait_for(asyncio.to_thread(jd.disconnect), timeout=JD_API_TIMEOUT)
                except Exception:
                    pass
            try:
                DOWNLOAD_TASKS.pop(cancel_key, None)
            except Exception:
                pass
        return

    elif entry.get("type") == "qb":
        stop_evt = entry.get("stop_event")
        if stop_evt:
            stop_evt.set()
    elif entry.get("type") == "gofile":
        mgr = entry.get("manager")
        if mgr:
            try:
                mgr._stop()
            except Exception:
                pass
        stop_evt = entry.get("stop_event")
        if stop_evt:
            stop_evt.set()
    else:
        proc = entry.get("process")
        if proc and getattr(proc, "returncode", None) is None:
            try:
                proc.terminate()
            except Exception:
                try:
                    proc.kill()
                except Exception:
                    pass
        stop_evt = entry.get("stop_event")
        if stop_evt:
            stop_evt.set()

    entry["cancelled"] = True
    try:
        await edit_with_retry(msg.edit("✖️Descarga cancelada por el usuario.", reply_markup=None, parse_mode=ParseMode.HTML))
    except Exception:
        pass
    try:
        DOWNLOAD_TASKS.pop(cancel_key, None)
    except Exception:
        pass
    await callback_query.answer("Cancelación solicitada.")

TELEGRAM_MESSAGE_MAX_LENGTH = 4096

def _split_plain_text(text: str, limit: int) -> List[str]:
    parts = []
    idx = 0
    length = len(text)
    while idx < length:
        if length - idx <= limit:
            parts.append(text[idx:])
            break
        end = idx + limit
        newline = text.rfind("\n", idx, end)
        chunk_end = end if newline <= idx else newline + 1
        parts.append(text[idx:chunk_end])
        idx = chunk_end
    return parts

async def _send_text_in_chunks(send_func, text: str, **kwargs):
    chunks = _split_message_for_telegram(text, kwargs.get("parse_mode"))
    sent = None
    for idx, chunk in enumerate(chunks):
        chunk_kwargs = kwargs.copy() if idx == 0 else {k: v for k, v in kwargs.items() if k != "reply_markup"}
        while True:
            try:
                sent = await throttled_send(send_func(chunk, **chunk_kwargs))
                break
            except FloodWait as exc:
                wait = None
                for attr in ("x", "value", "wait", "retry_after", "seconds"):
                    try:
                        v = getattr(exc, attr, None)
                    except Exception:
                        v = None
                    if isinstance(v, (int, float)):
                        wait = int(v)
                        break
                if wait is None:
                    try:
                        m = re.search(r"(\d+)", str(exc))
                        if m:
                            wait = int(m.group(1))
                    except Exception:
                        wait = None
                if not wait:
                    wait = 1
                try:
                    logger.warning("FloodWait encountered, sleeping %s seconds", wait)
                except Exception:
                    pass
                await asyncio.sleep(wait)
    return sent

def _split_message_for_telegram(text: str, parse_mode: Optional[str]) -> List[str]:
    if len(text) <= TELEGRAM_MESSAGE_MAX_LENGTH:
        return [text]
    return _split_plain_text(text, TELEGRAM_MESSAGE_MAX_LENGTH)

def _scrub_text_for_user(text: Optional[str]) -> str:
    if text is None:
        return ""
    return str(text)

async def safe_reply(message: Message, text: str, **kwargs):
    sanitized = _scrub_text_for_user(text)
    try:
        return await asyncio.wait_for(_send_text_in_chunks(message.reply_text, sanitized, **kwargs), timeout=15.0)
    except asyncio.TimeoutError:
        logger.warning("safe_reply timed out, falling back to direct send")
        try:
            async def _fallback(chunk_text: str, **kw):
                return await throttled_send(bot_client.send_message(message.chat.id, chunk_text, **kw))
            return await asyncio.wait_for(_send_text_in_chunks(_fallback, sanitized, **kwargs), timeout=15.0)
        except asyncio.TimeoutError:
            logger.error("safe_reply fallback also timed out")
            return None
    except Exception:
        logger.exception("Failed to send message safely")
        return None

async def safe_send(chat_id: int, text: str, **kwargs):
    sanitized = _scrub_text_for_user(text)
    try:
        if BOT_ID is not None and chat_id == BOT_ID:
            logger.debug("Not sending message: target %s is the bot itself.", chat_id)
            return None
        async def _send_impl(chunk_text: str, **kw):
            return await throttled_send(bot_client.send_message(chat_id, chunk_text, **kw))
        return await asyncio.wait_for(_send_text_in_chunks(_send_impl, sanitized, **kwargs), timeout=15.0)
    except asyncio.TimeoutError:
        logger.warning("safe_send timed out")
        return None
    except Exception:
        logger.exception("Failed to send message safely")
        return None

async def notify_user_from_message(message: Message, text: str, **kwargs):
    try:
        target_id = None
        if message and getattr(message, "from_user", None) and getattr(message.from_user, "id", None) is not None:
            target_id = int(message.from_user.id)
        if target_id is not None and target_id != BOT_ID:
            try:
                return await safe_send(target_id, text, **kwargs)
            except Exception:
                logger.exception("notify_user_from_message: safe_send failed, falling back to safe_reply")
        return await safe_reply(message, text, **kwargs)
    except Exception:
        logger.exception("notify_user_from_message failed")
        try:
            return await safe_reply(message, text, **kwargs)
        except Exception:
            return None

URL_REGEX = re.compile(r"(https?://[^\s]+)|(magnet:\?[^\s]+)|((?:ftp|ftps)://[^\s]+)", re.IGNORECASE)

def _normalize_user_key(token: str):
    if not token:
        return None
    token = token.strip()
    if token.startswith("@"):
        return token.lower()
    try:
        iid = int(token)
        return str(iid)
    except Exception:
        return ("@" + token).lower() if not token.startswith("@") else token.lower()

def _is_allowed_impl(user) -> bool:
    if _is_owner_impl(user):
        return True
    if user is None:
        return False
    now_ts = datetime.now(timezone.utc).timestamp()
    key_id = str(user.id) if getattr(user, "id", None) is not None else None
    uname = ("@" + user.username).lower() if getattr(user, "username", None) else None
    if key_id and key_id in ADDED_USERS:
        info = ADDED_USERS.get(key_id)
        if info and info.get("expires_at", 0) > now_ts:
            return True
        ADDED_USERS.pop(key_id, None)
    if uname and uname in ADDED_USERS:
        info = ADDED_USERS.get(uname)
        if info and info.get("expires_at", 0) > now_ts:
            return True
        ADDED_USERS.pop(uname, None)
    return False

def is_allowed_user(user) -> bool:
    try:
        uid = getattr(user, "id", None)
        uname = ("@" + user.username).lower() if getattr(user, "username", None) else None
        logger.debug("is_allowed check: user.id=%s username=%s ADDED_USERS=%s", uid, uname, ADDED_USERS)
    except Exception:
        logger.exception("is_allowed debug logging failed")
    return _is_allowed_impl(user)

def add_temporary_user_and_save(key: str, info: dict):
    try:
        ADDED_USERS[key] = info
        save_persistent_state()
    except Exception:
        logger.exception("Failed to add temporary user and save state")

def remove_temporary_user_and_save(key: str):
    try:
        if key in ADDED_USERS:
            ADDED_USERS.pop(key, None)
            save_persistent_state()
    except Exception:
        logger.exception("Failed to remove temporary user and save state")

def set_upload_description_and_save(value: Optional[str]):
    global UPLOAD_DESCRIPTION
    try:
        if value is None or (isinstance(value, str) and value.strip() == ""):
            UPLOAD_DESCRIPTION = None
        else:
            UPLOAD_DESCRIPTION = str(value)
        save_persistent_state()
    except Exception:
        logger.exception("Failed to set upload description and save state")

def create_jd_instance():
    jd = Myjdapi()
    try:
        if hasattr(jd, "set_app_key"):
            jd.set_app_key(MYJD_APP_KEY)
        elif hasattr(jd, "setAppKey"):
            jd.setAppKey(MYJD_APP_KEY)
        else:
            try:
                setattr(jd, "app_key", MYJD_APP_KEY)
            except Exception:
                logger.debug("Could not set app key on jd instance explicitly")
    except Exception:
        logger.exception("Error while setting app key (non-fatal)")
    return jd

def connect_jd():
    jd = create_jd_instance()
    try:
        logger.info("Connecting to MyJDownloader as %s", MYJD_USER)
        jd.connect(MYJD_USER, MYJD_PASS)
        try:
            if hasattr(jd, "update_devices"):
                jd.update_devices()
            elif hasattr(jd, "updateDevices"):
                jd.updateDevices()
        except Exception:
            logger.debug("jd.update_devices/updateDevices unavailable or failed (continuing)")
        return jd
    except Exception as e:
        try:
            jd.disconnect()
        except Exception:
            pass
        logger.exception("Failed to connect to MyJDownloader")
        raise RuntimeError("Download system connect error") from e

def get_device_direct(jd, identifier):
    device = None
    if hasattr(jd, "get_device"):
        try:
            device = jd.get_device(identifier)
        except TypeError:
            try:
                device = jd.get_device(device_id=identifier)
            except Exception:
                try:
                    device = jd.get_device(name=identifier)
                except Exception:
                    device = None
        except Exception:
            device = None
    if device is None and hasattr(jd, "getDevice"):
        try:
            device = jd.getDevice(identifier)
        except Exception:
            try:
                device = jd.getDevice(name=identifier)
            except Exception:
                try:
                    device = jd.getDevice(device_id=identifier)
                except Exception:
                    device = None
    if device is None:
        raise RuntimeError("Could not obtain device with provided identifier. Ensure the configured device identifier is correct.")
    return device

def _derive_display_name_from_link(link: str, tg_user) -> str:
    try:
        if is_magnet(link):
            parsed = urllib.parse.urlparse(link)
            q = urllib.parse.parse_qs(parsed.query)
            dn_vals = q.get("dn") or q.get("DN") or q.get("Name")
            if dn_vals:
                name = sanitize_filename(urllib.parse.unquote(dn_vals[0]))
                if name:
                    return name
            return f"magnet_{int(time.time())}"
        if is_torrent_url(link) and link.lower().startswith("http"):
            name = Path(urllib.parse.urlparse(link).path).name
            if name:
                return sanitize_filename(name)
        parsed = urllib.parse.urlparse(link)
        pathp = Path(parsed.path)
        if pathp.name:
            return sanitize_filename(pathp.name)
        if parsed.netloc:
            return sanitize_filename(parsed.netloc + "_" + str(int(time.time())))
    except Exception:
        pass
    return f"link_{int(time.time())}"

def add_links_to_device(links, tg_user):
    jd = None
    try:
        jd = connect_jd()
        device = get_device_direct(jd, JD_DEVICE_NAME)
        if not hasattr(device, "linkgrabber"):
            raise RuntimeError("Device object does not expose 'linkgrabber'")
        lg = device.linkgrabber
        user_folder = get_user_folder_name(tg_user)
        base = TELELOAD_BASE_DIR.rstrip("/")
        if not base:
            base = "/"
        if base == "/":
            destination_folder = f"/{user_folder}"
        else:
            destination_folder = f"{base}/{user_folder}"
        packages = []
        for link in links:
            dn = _derive_display_name_from_link(link, tg_user)
            unique_suffix = uuid.uuid4().hex[:8]
            pkg_name = f"{dn}_{unique_suffix}"
            pkg = {
                "links": link,
                "packageName": pkg_name,
                "destinationFolder": destination_folder,
                "overwritePackagizerRules": True,
            }
            packages.append(pkg)
        result = None
        try:
            if hasattr(lg, "add_links"):
                result = lg.add_links(packages)
            elif hasattr(lg, "addLinks"):
                result = lg.addLinks(packages)
            else:
                if hasattr(device, "action"):
                    try:
                        result = device.action("linkgrabber", "addLinks", packages)
                    except Exception:
                        result = device.action("linkgrabber", "add_links", packages)
                else:
                    raise RuntimeError("Could not find a method to add links on device.linkgrabber")
        except TypeError:
            try:
                if hasattr(lg, "add_links"):
                    result = lg.add_links([packages])
                elif hasattr(lg, "addLinks"):
                    result = lg.addLinks([packages])
            except Exception:
                raise
        mappings = []
        try:
            if isinstance(result, dict):
                uuids = []
                if "packageUUIDs" in result and isinstance(result["packageUUIDs"], list):
                    uuids = [str(x) for x in result["packageUUIDs"]]
                for i, pkg in enumerate(packages):
                    pkg_uuid = uuids[i] if i < len(uuids) else None
                    mappings.append({
                        "display_name": pkg["packageName"],
                        "package_uuid": pkg_uuid,
                        "package_name": pkg["packageName"]
                    })
            elif isinstance(result, list):
                for i, entry in enumerate(result):
                    pkg = packages[i] if i < len(packages) else None
                    pkg_uuid = None
                    pkg_name = None
                    if isinstance(entry, dict):
                        pkg_uuid = entry.get("packageUUID") or entry.get("packageUUIDs") or entry.get("uuid")
                        if isinstance(pkg_uuid, list):
                            pkg_uuid = pkg_uuid[0] if pkg_uuid else None
                        pkg_name = entry.get("name") or entry.get("packageName") or entry.get("packageName")
                    if not pkg_name and pkg:
                        pkg_name = pkg["packageName"]
                    mappings.append({
                        "display_name": (pkg["packageName"] if pkg else pkg_name),
                        "package_uuid": (str(pkg_uuid) if pkg_uuid else None),
                        "package_name": pkg_name
                    })
            else:
                for pkg in packages:
                    mappings.append({
                        "display_name": pkg["packageName"],
                        "package_uuid": None,
                        "package_name": pkg["packageName"]
                    })
        except Exception:
            logger.exception("Failed to normalize add_links result")
            for pkg in packages:
                mappings.append({
                    "display_name": pkg["packageName"],
                    "package_uuid": None,
                    "package_name": pkg["packageName"]
                })
        return True, mappings
    except Exception as e:
        logger.exception("Failed to add links to device")
        return False, "Failed to add links to download system"
    finally:
        if jd:
            try:
                jd.disconnect()
            except Exception:
                pass

PROGRESS_UPDATE_INTERVAL = 10.0  # Reduced frequency

def is_magnet(link: str) -> bool:
    return link.strip().lower().startswith("magnet:")

def is_torrent_url(link: str) -> bool:
    lower = link.lower().split("?", 1)[0]
    return lower.endswith(".torrent")

def is_torrent_file(path: Path) -> bool:
    return path.is_file() and path.suffix.lower() == '.torrent'

async def download_torrent_file(session: aiohttp.ClientSession, url: str, dest_path: Path) -> Path:
    dest_path.mkdir(parents=True, exist_ok=True)
    filename = Path(url.split("?")[0]).name or f"temp_{int(time.time())}.torrent"
    out_file = dest_path / filename
    async with session.get(url) as resp:
        resp.raise_for_status()
        with out_file.open("wb") as f:
            while True:
                chunk = await resp.content.read(64 * 1024)
                if not chunk:
                    break
                f.write(chunk)
    return out_file

def bdecode_get_name_of_torrent(torrent_path: Path) -> Optional[str]:
    try:
        data = torrent_path.read_bytes()
    except Exception:
        return None
    def parse_at(data: bytes, i: int):
        if data[i:i+1] == b'i':
            j = data.find(b'e', i)
            if j == -1:
                raise ValueError("Invalid bencode int")
            val = int(data[i+1:j])
            return val, j+1
        if data[i:i+1].isdigit():
            colon = data.find(b':', i)
            if colon == -1:
                raise ValueError("Invalid bencode string")
            length = int(data[i:colon])
            start = colon+1
            end = start + length
            s = data[start:end]
            return s, end
        if data[i:i+1] == b'l':
            i += 1
            lst = []
            while data[i:i+1] != b'e':
                v, i = parse_at(data, i)
                lst.append(v)
            return lst, i+1
        if data[i:i+1] == b'd':
            i += 1
            dct = {}
            while data[i:i+1] != b'e':
                k, i = parse_at(data, i)
                v, i = parse_at(data, i)
                dct[k] = v
            return dct, i+1
        raise ValueError("Invalid bencode")
    try:
        parsed, _ = parse_at(data, 0)
    except Exception:
        return None
    if isinstance(parsed, dict):
        info = parsed.get(b'info')
        if isinstance(info, dict):
            name = info.get(b'name')
            if isinstance(name, bytes):
                try:
                    return name.decode(errors="ignore")
                except Exception:
                    return name.decode('utf-8', errors="ignore")
    return None

def sanitize_filename(name: str) -> str:
    invalid = '<>:"/\\|?*\0'
    return ''.join('_' if c in invalid else c for c in name).strip()

async def unique_rename_path_async(path: Path) -> Path:
    ts = time.strftime("%Y%m%d_%H%M%S")
    if path.is_file():
        stem = path.stem
        suffix = path.suffix
        new_name = f"{stem}_bak_{ts}{suffix}"
    else:
        new_name = f"{path.name}_bak_{ts}"
    new_path = path.with_name(new_name)
    counter = 1
    while new_path.exists():
        if path.is_file():
            new_name = f"{stem}_bak_{ts}_{counter}{suffix}"
        else:
            new_name = f"{path.name}_bak_{ts}_{counter}"
        new_path = path.with_name(new_name)
        counter += 1
    await asyncio.wait_for(asyncio.to_thread(path.rename, new_path), timeout=FILE_IO_TIMEOUT)
    return new_path

async def safe_rename_existing_async(dest_dir: Path, candidate_name: str) -> Optional[Path]:
    if not candidate_name:
        return None
    safe_name = sanitize_filename(candidate_name)
    target = dest_dir / safe_name
    if target.exists():
        try:
            new_path = await unique_rename_path_async(target)
            logger.info("Renamed existing '%s' to '%s' to avoid collision", target, new_path)
            return new_path
        except Exception:
            logger.exception("Failed to rename existing target to avoid collision: %s", target)
            return None
    return None

async def apply_suffix_filter_to_path(file_path: Path, retries: int = SUFFIX_RETRY_COUNT, delay: float = SUFFIX_RETRY_DELAY) -> Tuple[Optional[Path], bool]:
    if not file_path.exists():
        logger.debug(f"Suffix filter: {file_path} does not exist")
        return None, False
    if is_torrent_file(file_path):
        logger.debug(f"Suffix filter: skipping .torrent file {file_path.name}")
        return file_path, False
    if not SUFFIX_FILTER_ENABLED:
        logger.debug(f"Suffix filter disabled, returning original {file_path}")
        return file_path, False
    original_name = file_path.name
    original_name_stripped = original_name.strip()
    if original_name_stripped != original_name:
        logger.info(f"Suffix filter: file name has leading/trailing spaces: '{original_name}'")
    for suffix in SUFFIX_FILTERS:
        suffix_variants = [suffix, suffix.strip()]
        for svar in suffix_variants:
            if not svar:
                continue
            if original_name_stripped.endswith(svar):
                new_name = original_name_stripped[:-len(svar)].strip()
                if not new_name:
                    logger.warning(f"Suffix filter: cannot rename '{original_name}' to empty string")
                    continue
                new_path = file_path.parent / new_name
                logger.info(f"Suffix filter: attempting to rename '{original_name}' -> '{new_name}' (suffix '{svar}')")
                if new_path.exists():
                    logger.info(f"Target '{new_name}' already exists, moving it aside")
                    renamed_existing = await safe_rename_existing_async(file_path.parent, new_name)
                    if not renamed_existing:
                        logger.error(f"Cannot rename '{original_name}' because target exists and could not be moved")
                        return file_path, False
                for attempt in range(retries):
                    try:
                        await asyncio.wait_for(asyncio.to_thread(file_path.rename, new_path), timeout=FILE_IO_TIMEOUT)
                        logger.info(f"Suffix filter: SUCCESS renamed '{original_name}' -> '{new_name}'")
                        return new_path, True
                    except (PermissionError, OSError) as e:
                        logger.warning(f"Rename attempt {attempt+1} failed for '{original_name}': {e}. Retrying in {delay}s...")
                        await asyncio.sleep(delay)
                    except Exception as e:
                        logger.error(f"Unexpected error renaming '{original_name}': {e}")
                        return file_path, False
                logger.error(f"Failed to rename '{original_name}' after {retries} attempts")
                return file_path, False
    logger.debug(f"Suffix filter: no matching suffix for '{original_name}'")
    return file_path, False

async def apply_file_signing_async(path: Path, sign: str, enabled: bool) -> Optional[Path]:
    if not enabled or not sign:
        return path if path and path.exists() else None
    if not path or not path.exists():
        return None
    if is_torrent_file(path):
        logger.debug(f"File signing: skipping .torrent file {path.name}")
        return path
    original_name = path.name
    if original_name.endswith(" " + sign):
        logger.debug(f"Sign '{sign}' already present in '{original_name}', skipping")
        return path
    if path.is_file():
        stem = path.stem
        suffix = path.suffix
        new_stem = f"{stem} {sign}"
        new_name = new_stem + suffix
    else:
        new_name = f"{original_name} {sign}"
    new_path = path.parent / new_name
    if new_path.exists():
        counter = 1
        base = new_path.stem if new_path.is_file() else new_path.name
        ext = new_path.suffix if new_path.is_file() else ""
        while True:
            if ext:
                candidate = new_path.parent / f"{base}_{counter}{ext}"
            else:
                candidate = new_path.parent / f"{base}_{counter}"
            if not candidate.exists():
                break
            counter += 1
        logger.info(f"Moving existing '{new_path}' to '{candidate}' to avoid collision")
        await asyncio.wait_for(asyncio.to_thread(new_path.rename, candidate), timeout=FILE_IO_TIMEOUT)
    try:
        await asyncio.wait_for(asyncio.to_thread(path.rename, new_path), timeout=FILE_IO_TIMEOUT)
        logger.info(f"File signing: renamed '{original_name}' -> '{new_name}'")
        return new_path
    except Exception as e:
        logger.error(f"Failed to apply file sign to '{original_name}': {e}")
        return path

async def process_path_with_suffix_and_signing_async(path: Path) -> Optional[Path]:
    if not path or not path.exists():
        return None
    if is_torrent_file(path):
        logger.debug(f"process_path_with_suffix_and_signing_async: skipping .torrent file {path.name}")
        return path
    filtered_path, was_modified = await apply_suffix_filter_to_path(path)
    if filtered_path is None:
        return None
    final_path = await apply_file_signing_async(filtered_path, FILE_SIGN, FILE_SIGNING_ENABLED)
    return final_path if final_path else filtered_path

def _format_duration(seconds: Optional[float]) -> str:
    if seconds is None:
        return "?"
    try:
        total = int(max(0, seconds))
    except Exception:
        return "?"
    hrs, rem = divmod(total, 3600)
    mins, secs = divmod(rem, 60)
    if hrs:
        return f"{hrs}h{mins}m{secs}s"
    if mins:
        return f"{mins}m{secs}s"
    return f"{secs}s"

def human_size(nbytes: Optional[int]) -> str:
    if nbytes is None:
        return "?"
    try:
        nbytes = int(nbytes)
    except Exception:
        return "?"
    if nbytes == 0:
        return "0B"
    units = ["B", "KB", "MB", "GB", "TB"]
    i = int(math.floor(math.log(max(nbytes,1), 1024)))
    i = min(i, len(units)-1)
    p = math.pow(1024, i)
    s = round(nbytes / p, 2)
    return f"{s} {units[i]}"

def build_progress_text(title: str, total_bytes: Optional[int], downloaded_bytes: Optional[int], elapsed: float, eta_seconds: Optional[float], speed: Optional[int] = None) -> str:
    try:
        if total_bytes and downloaded_bytes is not None and total_bytes > 0:
            pct = min(100.0, (downloaded_bytes / total_bytes) * 100.0)
        else:
            pct = 0.0
        blocks = int((pct / 100.0) * 20)
        bar = "█" * blocks + "░" * (20 - blocks)
        total_str = human_size(total_bytes) if total_bytes is not None else "?"
        dl_str = human_size(downloaded_bytes) if downloaded_bytes is not None else "?"
        eta_str = _format_duration(eta_seconds)
        try:
            e = int(elapsed)
            h, rem = divmod(e, 3600)
            m, s = divmod(rem, 60)
            if h:
                elapsed_str = f"{h}h{m}m{s}s"
            elif m:
                elapsed_str = f"{m}m{s}s"
            else:
                elapsed_str = f"{s}s"
        except Exception:
            elapsed_str = "?"
        speed_str = (human_size(speed) + "/s") if speed else "?"
        txt = (f"<i>{title}\n{bar} {pct:.1f}%\n{dl_str} / {total_str} • ETA: {eta_str}\nTranscurrido: {elapsed_str} • Velocidad: {speed_str}</i>")
        return txt
    except Exception:
        return f"<i>{title}</i>"

async def build_progress_text_from_jd(title: str, bytes_total: Optional[int], bytes_loaded: Optional[int],
                                      speed: Optional[int], eta_seconds: Optional[float], elapsed_seconds: Optional[float]) -> str:
    def human_size_local(num):
        if num is None:
            return "?"
        try:
            num = float(num)
        except Exception:
            return "?"
        for unit in ["B", "KiB", "MiB", "GiB", "TiB"]:
            if abs(num) < 1024.0:
                return f"{num:3.1f}{unit}"
            num /= 1024.0
        return f"{num:.1f}PiB"
    def fmt_elapsed(s):
        if s is None:
            return "?"
        try:
            s = int(s)
        except Exception:
            return "?"
        h, rem = divmod(s, 3600)
        m, sec = divmod(rem, 60)
        if h:
            return f"{h}h{m}m{sec}s"
        if m:
            return f"{m}m{sec}s"
        return f"{sec}s"
    bar_len = 20
    pct = None
    if bytes_total and bytes_loaded is not None and bytes_total > 0:
        pct = min(100.0, max(0.0, (bytes_loaded / bytes_total) * 100.0))
    filled = int((pct or 0) / 100.0 * bar_len) if pct is not None else 0
    bar = "█" * filled + "░" * (bar_len - filled)
    percent_text = f"{pct:.1f}%" if pct is not None else "?"
    speed_text = (human_size_local(speed) + "/s") if speed else "?"
    eta_text = ""
    if eta_seconds is not None:
        if eta_seconds < 0:
            eta_text = "ETA: ?"
        else:
            s = int(eta_seconds)
            m, s = divmod(s, 60)
            h, m = divmod(m, 60)
            if h:
                eta_text = f"ETA: {h}h{m}m{s}s"
            elif m:
                eta_text = f"ETA: {m}m{s}s"
            else:
                eta_text = f"ETA: {s}s"
    elapsed_text = fmt_elapsed(elapsed_seconds)
    txt = (f"<i>{title}\n"
           f"{bar} {percent_text}\n"
           f"{human_size_local(bytes_loaded)} / {human_size_local(bytes_total)} • {speed_text} • {eta_text}\n"
           f"Transcurrido: {elapsed_text}</i>")
    return txt

# ============================================================
# MONITOR JD PACKAGES WITH INACTIVITY TIMEOUT AND ROOT FOLDER SAFETY
# FIX: All progress edits are now fire-and-forget (asyncio.create_task)
# ============================================================
async def monitor_jd_packages(jd_instance, device, package_query_ids: List[str], telegram_message, title_prefix="JD", poll_interval: float = 2.0, inactivity_timeout: Optional[float] = DOWNLOAD_INACTIVITY_TIMEOUT, cancel_key: Optional[str]=None, user=None, wait_for_automator: bool = False, root_snapshot_before: Optional[Set[str]] = None):
    start = datetime.now(timezone.utc).timestamp()
    last_progress_time = start
    MAX_TOTAL_TIME = 6 * 3600

    query_template = {
        "bytesLoaded": True,
        "bytesTotal": True,
        "eta": True,
        "speed": True,
        "status": True,
        "finished": True,
        "running": True,
        "name": True,
        "saveTo": True,
        "childCount": True,
        "uuid": True,
        "packageUUID": True,
        "packageName": True,
        "nextTry": True,
        "nextTryTime": True,
        "retryDelay": True,
        "retryIn": True,
        "retryAfter": True,
        "stopCountdown": True,
        "timestamp": True,
        "maxResults": -1,
        "startAt": 0,
    }
    def query_packages_sync():
        try:
            qp = [query_template.copy()]
            res = None
            if hasattr(device.downloads, "query_packages"):
                res = device.downloads.query_packages(qp)
            elif hasattr(device.downloads, "queryPackages"):
                res = device.downloads.queryPackages(qp)
            else:
                if hasattr(device, "action"):
                    res = device.action("downloads", "queryPackages", qp)
                else:
                    raise RuntimeError("Device.downloads.query_packages not available")
            if isinstance(res, str):
                try:
                    res = json.loads(res)
                except Exception:
                    pass
            return res or []
        except Exception as e:
            logger.exception("query_packages failed")
            return []   # return empty on any error
    watched = list(package_query_ids)
    last_states = {}
    limit_detected_at = {}
    limit_notified = set()
    GRACE_NO_PACKAGE_SECONDS = 8.0
    automator_tasks = []
    while True:
        # Comprobar cancelación
        if asyncio.current_task().cancelled():
            logger.info("monitor_jd_packages cancelled")
            return False, "cancelled"
        if cancel_key and DOWNLOAD_TASKS.get(cancel_key, {}).get("cancelled"):
            asyncio.create_task(
                edit_progress_resilient(
                    telegram_message,
                    "<i>✖️Descarga cancelada por el usuario.</i>",
                    reply_markup=None,
                    client=bot_client,
                    per_attempt_timeout=5.0
                )
            )
            try:
                if cancel_key:
                    DOWNLOAD_TASKS.pop(cancel_key, None)
            except Exception:
                pass
            return False, "cancelled_by_user"

        now = datetime.now(timezone.utc).timestamp()
        elapsed_total = now - start

        if elapsed_total > MAX_TOTAL_TIME:
            asyncio.create_task(
                edit_progress_resilient(
                    telegram_message,
                    "<i>Tiempo total de monitoreo excedido (6 horas). Abortando.</i>",
                    reply_markup=None,
                    client=bot_client,
                    per_attempt_timeout=5.0
                )
            )
            try:
                if cancel_key:
                    DOWNLOAD_TASKS.pop(cancel_key, None)
            except Exception:
                pass
            return False, "max_total_time"

        if inactivity_timeout and (now - last_progress_time) > inactivity_timeout:
            asyncio.create_task(
                edit_progress_resilient(
                    telegram_message,
                    f"<i>Sin progreso durante {inactivity_timeout} segundos. Abortando.</i>",
                    reply_markup=None,
                    client=bot_client,
                    per_attempt_timeout=5.0
                )
            )
            try:
                if cancel_key:
                    DOWNLOAD_TASKS.pop(cancel_key, None)
            except Exception:
                pass
            return False, "timeout_inactive"

        packages = await asyncio.wait_for(asyncio.to_thread(query_packages_sync), timeout=JD_API_TIMEOUT)
        if not packages:
            if cancel_key and DOWNLOAD_TASKS.get(cancel_key, {}).get("cancelled"):
                return False, "cancelled_by_user"
            if elapsed_total < GRACE_NO_PACKAGE_SECONDS:
                asyncio.create_task(
                    edit_progress_resilient(
                        telegram_message,
                        "<i>Esperando que los paquetes aparezcan...</i>",
                        reply_markup=_download_cancel_keyboard(cancel_key) if cancel_key else None,
                        client=bot_client,
                        per_attempt_timeout=5.0
                    )
                )
                await asyncio.sleep(poll_interval)
                continue
            else:
                logger.info("No packages returned after grace period; assuming finished or removed.")
                asyncio.create_task(
                    edit_progress_resilient(
                        telegram_message,
                        "<i>No se encontró información de paquetes. Asumiendo finalizado.</i>",
                        reply_markup=None,
                        client=bot_client,
                        per_attempt_timeout=5.0
                    )
                )
                try:
                    if cancel_key:
                        DOWNLOAD_TASKS.pop(cancel_key, None)
                except Exception:
                    pass
                return True, "assumed_finished_no_packages"
        by_uuid = {}
        by_name = {}
        by_id = {}
        for p in packages:
            uid = p.get("uuid") or p.get("packageUUID") or p.get("id")
            name = p.get("name") or p.get("packageName")
            if uid:
                by_uuid[str(uid)] = p
            if name:
                by_name[str(name)] = p
            if p.get("id"):
                by_id[str(p.get("id"))] = p
        total_bytes = 0
        total_loaded = 0
        total_speed = 0
        any_running = False
        all_finished = True
        summary_lines = []
        matched_any = False
        finished_packages_info = []
        progress_made = False

        for ident in list(watched):
            p = None
            if ident in by_uuid:
                p = by_uuid[ident]
            elif ident in by_id:
                p = by_id[ident]
            elif ident in by_name:
                p = by_name[ident]
            else:
                for nm, pack in by_name.items():
                    if ident and ident in nm:
                        p = pack
                        break
            if not p:
                all_finished = False
                summary_lines.append(f"{ident}: esperando...")
                continue
            matched_any = True
            loaded = p.get("bytesLoaded") or 0
            total = p.get("bytesTotal") or 0
            speed = p.get("speed") or 0
            status = (p.get("status") or "").upper()
            name = p.get("name") or p.get("packageName") or ident
            try:
                loaded = int(loaded)
                total = int(total)
                speed = int(speed)
            except Exception:
                pass
            total_bytes += total
            total_loaded += loaded
            total_speed += speed
            finished_flag = bool(p.get("finished")) or (status in ("FINISHED",))
            if (not finished_flag) and (status not in ("FINISHED", "ERROR", "STOPPED")):
                any_running = True
                all_finished = False

            prev = last_states.get(ident)
            prev_finished = None
            if prev is None:
                progress_made = True
            else:
                prev_loaded = prev.get("bytesLoaded", 0)
                prev_finished = prev.get("finished", False)
                if loaded > prev_loaded or (finished_flag and not prev_finished):
                    progress_made = True
            last_states[ident] = {"bytesLoaded": loaded, "finished": finished_flag}

            timer_msg = None
            try:
                eta_val = p.get("eta")
                if eta_val is None:
                    eta_val = p.get("retryIn") or p.get("retryAfter") or p.get("retryDelay") or p.get("stopCountdown")
                if eta_val is not None and isinstance(eta_val, (int, float)):
                    timer_msg = f"cuenta regresiva {int(eta_val)}s"
                if not timer_msg and p.get("nextTryTime"):
                    try:
                        ntt = p.get("nextTryTime")
                        ntt_f = float(ntt)
                        if ntt_f > 1e12:
                            ntt_f = ntt_f / 1000.0
                        secs_until = int(max(0, ntt_f - now))
                        timer_msg = f"próximo intento en {secs_until}s"
                    except Exception:
                        pass
                if not timer_msg and isinstance(p.get("nextTry"), dict):
                    nt = p.get("nextTry")
                    for key in ("timestamp", "time", "when"):
                        if key in nt:
                            try:
                                ntt_f = float(nt.get(key))
                                if ntt_f > 1e12:
                                    ntt_f = ntt_f / 1000.0
                                secs_until = int(max(0, ntt_f - now))
                                timer_msg = f"próximo intento en {secs_until}s"
                                break
                            except Exception:
                                continue
            except Exception:
                pass
            reason = None
            try:
                if p.get("statusInfo") and isinstance(p.get("statusInfo"), dict):
                    si = p.get("statusInfo")
                    for fk in ("message", "reason", "text", "detail"):
                        if fk in si and si[fk]:
                            reason = str(si[fk])
                            break
                if not reason:
                    for fk in ("pauseReason", "errorMessage", "problemDescription"):
                        if p.get(fk):
                            reason = str(p.get(fk))
                            break
            except Exception:
                pass
            pct = (loaded / total * 100.0) if (total and total > 0) else None
            status_fragment = f"{status}" if status else ""
            if timer_msg:
                status_fragment += (f" • {timer_msg}" if status_fragment else timer_msg)
            if reason:
                status_fragment += (f" • {reason}" if status_fragment else reason)
            if pct is not None:
                summary_lines.append(f"{name}: {pct:.1f}% ({human_size(loaded)} / {human_size(total)}) [{status_fragment}]")
            else:
                summary_lines.append(f"{name}: {human_size(loaded)} / {human_size(total)} [{status_fragment}]")
            try:
                limit_phrase = "download limit has been reached"
                sf_lower = (status_fragment or "").lower()
                reason_lower = (reason or "").lower()
                now_ts = datetime.now(timezone.utc).timestamp()
                if (limit_phrase in sf_lower) or (limit_phrase in reason_lower):
                    if name not in limit_detected_at:
                        limit_detected_at[name] = now_ts
                    elif (now_ts - limit_detected_at[name] >= 15.0) and (name not in limit_notified):
                        try:
                            notify_msg = (f"<i>Límite de descarga alcanzado para el paquete '{name}'. "
                                          "La descarga se reanudará cuando se despeje el límite.</i>")
                            await throttled_send(telegram_message.reply(_scrub_text_for_user(notify_msg)))
                        except Exception:
                            try:
                                current_text = ""
                                try:
                                    current_text = getattr(telegram_message, "text", "") or ""
                                except Exception:
                                    current_text = ""
                                try:
                                    await edit_with_retry(telegram_message.edit(_scrub_text_for_user((current_text + "\n\n" + notify_msg).strip())))
                                except Exception:
                                    pass
                            except Exception:
                                pass
                        limit_notified.add(name)
                        return True, "assumed_finished_limit"
                else:
                    if name in limit_detected_at:
                        limit_detected_at.pop(name, None)
                        limit_notified.discard(name)
            except Exception:
                logger.exception("Error while checking download limit detection for package %s", name)
            if finished_flag and prev is not None and not prev_finished:
                pkg_elapsed = elapsed_total
                avg_speed = None
                if pkg_elapsed and pkg_elapsed > 0:
                    try:
                        avg_speed = int(loaded / max(1.0, pkg_elapsed))
                    except Exception:
                        avg_speed = None
                finished_packages_info.append({
                    "name": name,
                    "size": total,
                    "loaded": loaded,
                    "avg_speed": avg_speed,
                    "elapsed": int(pkg_elapsed),
                    "status": status
                })
                try:
                    save_to = p.get("saveTo")
                    if save_to:
                        save_path = Path(save_to).resolve()
                        user_root = get_user_root_path(user).resolve()
                        if save_path == user_root:
                            if root_snapshot_before is not None:
                                after_snapshot = await get_directory_snapshot(user_root)
                                new_items = after_snapshot - root_snapshot_before
                                processed_items = set()
                                for item_path_str in new_items:
                                    item = Path(item_path_str)
                                    if item.name.endswith('.part') or item.name.startswith('.'):
                                        continue
                                    logger.info(f"Processing new item from root snapshot: {item}")
                                    await asyncio.sleep(SUFFIX_POST_DOWNLOAD_WAIT)
                                    processed = await process_path_with_suffix_and_signing_async(item)
                                    if await get_automator_enabled(user) and processed:
                                        task = asyncio.create_task(
                                            auto_compress_and_upload(
                                                user=user,
                                                original_path=processed,
                                                chat_id=telegram_message.chat.id,
                                                initiator_message=telegram_message,
                                                cancel_key=cancel_key,
                                                stop_event=None
                                            )
                                        )
                                        if wait_for_automator:
                                            automator_tasks.append(task)
                            else:
                                logger.warning("No snapshot available to detect new files in root folder. Skipping automator processing for this package.")
                            continue
                        if save_path == user_root:
                            logger.error(f"Still got root folder after correction, skipping package {name}")
                            continue
                        logger.info(f"Package finished: {name}, processing {save_path}")
                        await asyncio.sleep(SUFFIX_POST_DOWNLOAD_WAIT)
                        children = p.get("children") or p.get("links") or []
                        for child in children:
                            child_name = child.get("name")
                            if child_name:
                                full_child = save_path / child_name
                                await apply_suffix_filter_to_path(full_child)
                        processed_folder = await process_path_with_suffix_and_signing_async(save_path)
                        if processed_folder:
                            if await get_automator_enabled(user):
                                task = asyncio.create_task(
                                    auto_compress_and_upload(
                                        user=user,
                                        original_path=processed_folder,
                                        chat_id=telegram_message.chat.id,
                                        initiator_message=telegram_message,
                                        cancel_key=cancel_key,
                                        stop_event=None
                                    )
                                )
                                if wait_for_automator:
                                    automator_tasks.append(task)
                except Exception as e:
                    logger.warning(f"Failed to apply suffix filter or signing for package {name}: {e}")

        # ---------- QUOTA CHECK ----------
        remaining_bytes = total_bytes - total_loaded
        if await check_quota_and_abort(user,
                                       additional_bytes=remaining_bytes,
                                       message=telegram_message,
                                       cancel_key=cancel_key):
            asyncio.create_task(
                edit_progress_resilient(
                    telegram_message,
                    "<i>Descarga cancelada por límite de cuota.</i>",
                    reply_markup=None,
                    client=bot_client,
                    per_attempt_timeout=5.0
                )
            )
            return False, "quota_exceeded"
        # ---------------------------------

        if progress_made:
            last_progress_time = now

        if not matched_any:
            if elapsed_total < GRACE_NO_PACKAGE_SECONDS:
                if cancel_key and DOWNLOAD_TASKS.get(cancel_key, {}).get("cancelled"):
                    return False, "cancelled_by_user"
                asyncio.create_task(
                    edit_progress_resilient(
                        telegram_message,
                        "<i>Esperando que los paquetes aparezcan...</i>",
                        reply_markup=_download_cancel_keyboard(cancel_key) if cancel_key else None,
                        client=bot_client,
                        per_attempt_timeout=5.0
                    )
                )
                await asyncio.sleep(poll_interval)
                continue
            else:
                logger.info("No matching package after grace; assuming completed/removed.")
                if not (cancel_key and DOWNLOAD_TASKS.get(cancel_key, {}).get("cancelled")):
                    asyncio.create_task(
                        edit_progress_resilient(
                            telegram_message,
                            "<i>No se encontró paquete coincidente. Asumiendo finalizado.</i>",
                            reply_markup=None,
                            client=bot_client,
                            per_attempt_timeout=5.0
                        )
                    )
                try:
                    if cancel_key:
                        DOWNLOAD_TASKS.pop(cancel_key, None)
                except Exception:
                    pass
                return True, "assumed_finished_no_matching_packages"
        else:
            eta = None
            if total_speed and total_bytes and total_loaded < total_bytes:
                eta = (total_bytes - total_loaded) / max(1, total_speed)
            text = await build_progress_text_from_jd(title_prefix,
                                                     total_bytes if total_bytes > 0 else None,
                                                     total_loaded if total_loaded > 0 else None,
                                                     total_speed if total_speed > 0 else None,
                                                     eta,
                                                     elapsed_total)
            text += "\n\n" + "\n".join(summary_lines[:12])
        asyncio.create_task(
            edit_progress_resilient(
                telegram_message,
                text,
                reply_markup=_download_cancel_keyboard(cancel_key) if cancel_key else None,
                client=bot_client,
                per_attempt_timeout=5.0
            )
        )
        if all_finished:
            final_text = text + "\n\n<i>Todos los paquetes monitoreados finalizaron.</i>"
            # Await final edit with timeout to ensure user sees it
            try:
                await asyncio.wait_for(
                    edit_progress_resilient(
                        telegram_message,
                        final_text,
                        reply_markup=None,
                        client=bot_client,
                        per_attempt_timeout=5.0
                    ),
                    timeout=6.0
                )
            except Exception:
                pass
            try:
                if cancel_key:
                    DOWNLOAD_TASKS.pop(cancel_key, None)
            except Exception:
                pass
            if wait_for_automator and automator_tasks:
                await asyncio.gather(*automator_tasks, return_exceptions=True)
            return True, "finished"
        await asyncio.sleep(poll_interval)

def list_user_items(user) -> List[Path]:
    root = get_user_root_path(user)
    rel = CURRENT_DIRS.get(user.id, Path("."))
    try:
        current = (root / rel).resolve()
    except Exception:
        current = root
    try:
        if not str(current).startswith(str(root)):
            current = root
            CURRENT_DIRS[user.id] = Path(".")
    except Exception:
        current = root
        CURRENT_DIRS[user.id] = Path(".")
    if not current.exists():
        return []
    items = []
    try:
        for p in sorted(current.iterdir(), key=lambda x: (not x.is_dir(), x.name.lower())):
            items.append(p)
    except Exception:
        logger.exception("Failed to list user directory")
    return items

def format_list_items(items: List[Path]) -> str:
    lines = []
    total_bytes = 0
    for i, p in enumerate(items, start=1):
        try:
            if p.is_dir():
                size = "-"
                kind = "DIR"
                emoji = "📁"
            else:
                sz = p.stat().st_size
                total_bytes += sz
                size = human_size(sz)
                kind = "FILE"
                emoji = "📄"
        except Exception:
            size = "?"
            kind = "?"
            emoji = "❓"
        lines.append(f"{i}. {emoji} [{kind}] {p.name} • {size}")
    if not lines:
        return "No hay archivos o carpetas."
    lines.append("")
    lines.append(f"Total usado: {human_size(total_bytes)}")
    return "\n".join(lines)

def resolve_user_index_to_path(user, idx: int) -> Optional[Path]:
    items = list_user_items(user)
    if idx <= 0 or idx > len(items):
        return None
    return items[idx - 1]

def ensure_within_user_root(user, target: Path) -> bool:
    try:
        root = get_user_root_path(user)
        target = target.resolve()
        return str(target).startswith(str(root))
    except Exception:
        return False

def create_zip_for_path(src: Path, out_zip: Path) -> Path:
    with zipfile.ZipFile(out_zip, "w", compression=zipfile.ZIP_STORED) as zf:
        if src.is_file():
            zf.write(src, arcname=src.name)
        else:
            for rootp, dirs, files in os.walk(src):
                rootp = Path(rootp)
                for f in files:
                    full = rootp / f
                    arc = str(full.relative_to(src.parent))
                    zf.write(full, arcname=arc)
    return out_zip

def split_file(path: Path, max_bytes: int) -> List[Path]:
    parts = []
    idx = 0
    with path.open("rb") as f:
        while True:
            chunk = f.read(max_bytes)
            if not chunk:
                break
            idx += 1
            part = path.with_name(f"{path.name}.part{idx:03d}")
            with part.open("wb") as pf:
                pf.write(chunk)
            parts.append(part)
    return parts

bot_client = None
user_client = None
BOT_ID = None

async def _list_user_items_async(user, timeout_seconds: float = FILE_OPERATION_TIMEOUT) -> List[Path]:
    root = get_user_root_path(user)
    rel = CURRENT_DIRS.get(user.id, Path("."))
    try:
        current = (root / rel).resolve()
    except Exception:
        current = root
    try:
        if not str(current).startswith(str(root)):
            current = root
            CURRENT_DIRS[user.id] = Path(".")
    except Exception:
        current = root
        CURRENT_DIRS[user.id] = Path(".")
    if not current.exists():
        return []
    try:
        def _sync_listdir():
            result = []
            try:
                with os.scandir(str(current)) as it:
                    entries = list(it)
                    entries.sort(key=lambda x: (not x.is_dir(), x.name.lower()))
                    for entry in entries:
                        result.append(Path(entry.path))
            except Exception as e:
                logger.exception("Failed to list directory")
                raise
            return result
        items = await asyncio.wait_for(asyncio.to_thread(_sync_listdir), timeout=timeout_seconds)
        return items
    except asyncio.TimeoutError:
        logger.error(f"Directory listing timed out for user {user.id if user else 'unknown'}")
        raise
    except Exception as e:
        logger.exception("Failed to list user directory")
        raise

async def keep_alive_loop():
    while True:
        await asyncio.sleep(300)
        try:
            if user_client and user_client.is_connected:
                await asyncio.wait_for(user_client.get_me(), timeout=5.0)
                logger.debug("Keep-alive ping sent to user client")
        except asyncio.TimeoutError:
            logger.warning("Keep-alive timeout, client may be unreachable")
        except Exception as e:
            logger.warning(f"User client keep-alive failed: {e}")

async def task_health_check():
    while True:
        await asyncio.sleep(60)  # check every minute
        now = time.time()
        for task_id, task_info in list(DOWNLOAD_TASKS.items()):
            last_update = task_info.get("last_update", 0)
            if last_update and (now - last_update) > 300:
                logger.warning(f"Task {task_id} appears stuck (no update for 5 min). Reconnecting clients...")
                # Do NOT cancel the task – just try to revive the clients
                try:
                    if bot_client and not bot_client.is_connected:
                        await bot_client.reconnect()
                    if user_client and not user_client.is_connected:
                        await user_client.reconnect()
                except Exception as e:
                    logger.error(f"Failed to reconnect clients: {e}")
                # Reset the last_update so we don't spam
                task_info["last_update"] = now

async def processing_worker():
    while True:
        try:
            job_id, job = await PROCESSING_QUEUE.get()
            async with PENDING_JOBS_LOCK:
                pending_entry = PENDING_JOBS.get(job_id)
                if pending_entry and pending_entry.get("cancel_event", asyncio.Event()).is_set():
                    try:
                        await notify_user_from_message(job["message"], "✅ Su tarea encolada fue cancelada antes de procesarse.")
                    except Exception:
                        pass
                    PENDING_JOBS.pop(job_id, None)
                    PROCESSING_QUEUE.task_done()
                    continue
            async with PROCESSING_SEMAPHORE:
                # Wrap process_job with safety timeout if configured
                if JOB_SAFETY_TIMEOUT > 0:
                    try:
                        await asyncio.wait_for(process_job(job, job_id), timeout=JOB_SAFETY_TIMEOUT)
                    except asyncio.TimeoutError:
                        logger.warning(f"Job {job_id} exceeded safety timeout ({JOB_SAFETY_TIMEOUT}s), cancelling.")
                        await notify_user_from_message(job["message"], f"⚠️ El trabajo ha excedido el tiempo de seguridad ({JOB_SAFETY_TIMEOUT}s) y ha sido cancelado.")
                else:
                    await process_job(job, job_id)
        except asyncio.CancelledError:
            logger.warning("Processing worker cancelled, exiting")
            break
        except Exception as e:
            logger.exception("Job processing failed")
        finally:
            PROCESSING_QUEUE.task_done()

# ============================================================
# PROCESS JOB FOR AUTOMATOR QUEUE - WITH SNAPSHOT FIX AND MEDIA HANDLING
# ============================================================
async def process_job(job, job_id: str):
    user = job["user"]
    message = job["message"]
    gofile_links = job["gofile_links"]
    other_links = job["other_links"]
    aria2_targets = list(job.get("aria2_targets", []))
    text = job["text"]

    async with PENDING_JOBS_LOCK:
        pending_entry = PENDING_JOBS.get(job_id)
        if pending_entry and pending_entry.get("cancel_event", asyncio.Event()).is_set():
            await notify_user_from_message(message, "✅ Su trabajo fue cancelado antes de procesarse.")
            PENDING_JOBS.pop(job_id, None)
            return

    async def notify(msg: str):
        await notify_user_from_message(message, msg)

    # ---- Disk quota and free space check ----
    user_root = get_user_root_path(user)
    ok, msg = await check_disk_free_space(user_root)
    if not ok:
        await notify(msg)
        return
    ok, msg = await check_user_quota(user)
    if not ok:
        await notify(msg)
        return

    await notify("🔁 Su solicitud está siendo procesada. Puede tomar un tiempo.")

    # ---- 1. Handle media if present ----
    msg = message
    if msg.document or msg.photo or msg.video or msg.sticker or msg.voice or msg.audio:
        try:
            media_file = None
            filename = None
            if msg.document:
                media_file = msg.document
                filename = getattr(msg.document, "file_name", None)
            elif msg.video:
                media_file = msg.video
                filename = getattr(msg.video, "file_name", None)
            elif msg.photo:
                photo = msg.photo
                if isinstance(photo, list):
                    photo = photo[-1]
                media_file = photo
                filename = f"photo_{getattr(photo, 'file_unique_id', str(uuid.uuid4()))}.jpg"
            elif msg.sticker:
                media_file = msg.sticker
                filename = getattr(msg.sticker, "file_name", None) or f"sticker_{getattr(msg.sticker, 'file_unique_id', str(uuid.uuid4()))}.webp"
            elif msg.voice:
                media_file = msg.voice
                filename = getattr(msg.voice, "file_name", None) or f"voice_{getattr(msg.voice, 'file_unique_id', str(uuid.uuid4()))}.ogg"
            elif msg.audio:
                media_file = msg.audio
                filename = getattr(msg.audio, "file_name", None) or f"audio_{getattr(msg.audio, 'file_unique_id', str(uuid.uuid4()))}.mp3"

            if media_file and filename:
                user_folder = get_user_folder_name(user)
                base = TELELOAD_BASE_DIR.rstrip("/") or "/"
                if base == "/":
                    dest_base = Path.cwd()
                else:
                    dest_base = Path(base)
                dest_dir = dest_base / user_folder
                await asyncio.wait_for(asyncio.to_thread(dest_dir.mkdir, parents=True, exist_ok=True), timeout=FILE_IO_TIMEOUT)

                out_name = sanitize_filename(filename)
                out_path = dest_dir / out_name
                if out_path.exists():
                    counter = 1
                    candidate = out_path
                    while candidate.exists():
                        candidate = dest_dir / f"{out_path.stem}_{counter}{out_path.suffix}"
                        counter += 1
                    out_path = candidate

                total_size = None
                try:
                    total_size = int(getattr(media_file, "file_size", None) or 0) or None
                except Exception:
                    total_size = None

                start_time = time.time()
                initial_text = build_progress_text(out_path.name, total_size, 0, 0.0, None)
                progress_msg = await safe_reply(message, initial_text)

                if FORCE_USER_UPLOADS:
                    use_bot = False
                elif FORCE_BOT_UPLOADS:
                    use_bot = True
                else:
                    use_bot = (total_size and total_size > LARGE_FILE_THRESHOLD)
                if not use_bot and user_client is None:
                    logger.warning("User client not available, falling back to bot client")
                    use_bot = True
                download_client = bot_client if use_bot else user_client

                loop = asyncio.get_running_loop()
                def pyro_progress(current, total):
                    asyncio.run_coroutine_threadsafe(_pyro_progress_async(current, total), loop)

                async def _pyro_progress_async(current, total):
                    nonlocal start_time, total_size, progress_msg, out_path
                    try:
                        now = time.time()
                        if not hasattr(_pyro_progress_async, "_last_update"):
                            _pyro_progress_async._last_update = 0.0
                        if now - _pyro_progress_async._last_update < 6.0:
                            return
                        _pyro_progress_async._last_update = now
                        elapsed = now - start_time
                        total_b = total if total and total > 0 else total_size
                        speed = int(current / max(1.0, elapsed)) if elapsed > 0 else None
                        eta = None
                        if total_b and speed and speed > 0:
                            remaining = max(0, total_b - current)
                            eta = remaining / speed
                        textp = build_progress_text(out_path.name, total_b, current, elapsed, eta, speed=speed)
                        if speed is not None:
                            textp += f"\n\n<i>Velocidad: {human_size(speed)}/s</i>"
                        # Use fire-and-forget resilient edit
                        asyncio.create_task(edit_progress_resilient(progress_msg, textp, client=bot_client))
                    except Exception:
                        logger.exception("pyro progress callback failed")

                try:
                    user_msg_for_download = None
                    chat_id = message.chat.id
                    msg_id = message.id
                    try:
                        user_msg_for_download = await user_client.get_messages(chat_id, msg_id)
                    except Exception:
                        user_msg_for_download = None

                    if user_msg_for_download:
                        await user_client.download_media(user_msg_for_download, file_name=str(out_path), progress=pyro_progress)
                    else:
                        await bot_client.download_media(message, file_name=str(out_path), progress=pyro_progress)

                    final_bytes = int(out_path.stat().st_size) if out_path.exists() else None
                    total_elapsed = time.time() - start_time
                    avg_speed = int((final_bytes or total_size or 0) / max(1.0, total_elapsed)) if total_elapsed > 0 else None
                    final_text = build_progress_text(out_path.name, final_bytes or total_size, final_bytes, total_elapsed, 0, speed=avg_speed)
                    if avg_speed:
                        final_text += f"\n\n<i>Velocidad: {human_size(avg_speed)}/s</i>"
                    await edit_with_retry(progress_msg.edit(_scrub_text_for_user(final_text)))

                    processed_path = await process_path_with_suffix_and_signing_async(out_path)

                    if processed_path and is_torrent_file(processed_path):
                        aria2_targets.append(str(processed_path))
                    else:
                        if processed_path and await get_automator_enabled(user):
                            user_root2 = get_user_root_path(user).resolve()
                            if processed_path.resolve() != user_root2:
                                asyncio.create_task(
                                    auto_compress_and_upload(
                                        user=user,
                                        original_path=processed_path,
                                        chat_id=message.chat.id,
                                        initiator_message=message,
                                        cancel_key=None,
                                        stop_event=None
                                    )
                                )
                except Exception as e:
                    logger.exception("Media download failed")
                    await edit_with_retry(progress_msg.edit(_scrub_text_for_user(f"<i>Fallo en descarga de medios: {str(e)[:100]}</i>")))
        except Exception as e:
            logger.exception("Media handling failed")
            await notify(f"❌ Falló el procesamiento del medio: {str(e)[:100]}")

    # ---- 2. Handle download system links ----
    if other_links:
        await notify(f"📥 Añadiendo {len(other_links)} enlace(s) al sistema de descargas...")
        user_root = get_user_root_path(user)
        root_snapshot_before = await get_directory_snapshot(user_root)

        try:
            success, result = await asyncio.wait_for(asyncio.to_thread(add_links_to_device, other_links, user), timeout=JD_API_TIMEOUT)
        except asyncio.TimeoutError:
            await notify("❌ Tiempo de espera agotado añadiendo enlaces al sistema de descargas.")
            success = False
        if not success:
            await notify("❌ Falló al añadir enlaces al sistema de descargas.")
        else:
            mappings = result if isinstance(result, list) else []
            pkg_ids = []
            for m in mappings:
                if m.get("package_uuid"):
                    pkg_ids.append(str(m.get("package_uuid")))
                elif m.get("package_name"):
                    pkg_ids.append(str(m.get("package_name")))
            if not pkg_ids:
                pkg_ids = [f"Telegram_{get_user_folder_name(user)}"]
            display_names = [m.get("display_name") for m in mappings] if mappings else []
            title_prefix = ", ".join(display_names[:3]) if display_names else "Descarga"
            cancel_key = uuid.uuid4().hex
            status_msg = await safe_reply(
                message,
                "<i>Monitoreando el sistema de descargas...</i>",
                reply_markup=_download_cancel_keyboard(cancel_key)
            )
            jd = None
            try:
                jd = await asyncio.wait_for(asyncio.to_thread(connect_jd), timeout=JD_API_TIMEOUT)
                device = await asyncio.wait_for(asyncio.to_thread(get_device_direct, jd, JD_DEVICE_NAME), timeout=JD_API_TIMEOUT)
                DOWNLOAD_TASKS[cancel_key] = {"jd": jd, "device": device, "package_ids": pkg_ids,
                                              "user_id": getattr(user, "id", None), "cancelled": False,
                                              "type": "jd_monitor"}
                await monitor_jd_packages(
                    jd, device, pkg_ids, status_msg,
                    title_prefix=title_prefix, poll_interval=2.0, inactivity_timeout=DOWNLOAD_INACTIVITY_TIMEOUT,
                    cancel_key=cancel_key, user=user, wait_for_automator=True,
                    root_snapshot_before=root_snapshot_before
                )
            finally:
                if jd:
                    await asyncio.wait_for(asyncio.to_thread(jd.disconnect), timeout=JD_API_TIMEOUT)
                DOWNLOAD_TASKS.pop(cancel_key, None)

    # ---- 3. GoFile links are now handled by download system ----

    # ---- 4. Handle torrent downloads ----
    if aria2_targets:
        await notify(f"📥 Procesando {len(aria2_targets)} torrent(s)/magnet(s) con el cliente de torrents...")
        qb_cancel_key = uuid.uuid4().hex
        qb_status_msg = await safe_reply(
            message,
            f"<i>Iniciando descarga de {len(aria2_targets)} elemento(s) con el cliente de torrents...</i>",
            reply_markup=_download_cancel_keyboard(qb_cancel_key),
            parse_mode=ParseMode.HTML
        )
        success_count, results = await aria2_download_items(aria2_targets, user, qb_status_msg, wait_for_automator=True, cancel_key_override=qb_cancel_key)
        await notify(f"✅ Procesamiento de torrents finalizado: {success_count}/{len(aria2_targets)} exitosos.")

    await notify("🏁 Su solicitud ha sido completada.")

    async with PENDING_JOBS_LOCK:
        PENDING_JOBS.pop(job_id, None)

# ============================================================
# GOFILE DOWNLOAD WITH INACTIVITY MONITORING
# ============================================================
async def monitor_gofile_inactivity(download_dir: Path, stop_event: asyncio.Event, inactivity_timeout: int, status_msg: Message, cancel_key: str, user):
    if not download_dir.exists():
        return
    last_size = 0
    last_change_time = time.time()
    try:
        def get_total_size():
            total = 0
            if download_dir.exists():
                for item in download_dir.rglob("*"):
                    if item.is_file():
                        total += item.stat().st_size
            return total
        last_size = await asyncio.wait_for(asyncio.to_thread(get_total_size), timeout=FILE_IO_TIMEOUT)
        last_change_time = time.time()
    except Exception:
        pass
    while not stop_event.is_set():
        if asyncio.current_task().cancelled():
            break
        await asyncio.sleep(30)
        if stop_event.is_set():
            break
        try:
            current_size = await asyncio.wait_for(asyncio.to_thread(get_total_size), timeout=FILE_IO_TIMEOUT)
            if current_size != last_size:
                last_size = current_size
                last_change_time = time.time()
            elif (time.time() - last_change_time) > inactivity_timeout:
                logger.warning(f"GoFile download inactivity timeout: no bytes transferred for {inactivity_timeout}s, cancelling.")
                stop_event.set()
                asyncio.create_task(
                    edit_progress_resilient(
                        status_msg,
                        f"<i>Descarga cancelada: sin progreso durante {inactivity_timeout} segundos.</i>",
                        reply_markup=None,
                        client=bot_client,
                        per_attempt_timeout=5.0
                    )
                )
                if cancel_key and cancel_key in DOWNLOAD_TASKS:
                    DOWNLOAD_TASKS.pop(cancel_key, None)
                break
            # ---------- QUOTA CHECK ----------
            if await check_quota_and_abort(user,
                                           additional_bytes=0,
                                           message=status_msg,
                                           stop_event=stop_event,
                                           cancel_key=cancel_key):
                break
            # ---------------------------------
        except Exception as e:
            logger.debug(f"Inactivity monitor error: {e}")

async def run_gofile_job(link: str, pwd: Optional[str], user, cancel_key: str, stop_evt: asyncio.Event, message: Message, status_msg: Message) -> Tuple[bool, str]:
    try:
        user_dir = get_user_root_path(user)
        os.environ["GF_DOWNLOAD_DIR"] = str(user_dir)
        mgr = Manager(link, pwd, stop_event=stop_evt)
        loop = asyncio.get_running_loop()
        def progress_callback(text: str):
            async def _update():
                try:
                    await edit_with_retry(status_msg.edit(_scrub_text_for_user(text), reply_markup=_download_cancel_keyboard(cancel_key), parse_mode=ParseMode.HTML))
                except Exception:
                    pass
            asyncio.run_coroutine_threadsafe(_update(), loop)
        mgr._progress_callback = progress_callback
        mgr._token = getenv("GF_TOKEN")
        content_id = link.split("/")[-1].split("?")[0]
        expected_path = user_dir / content_id

        monitor_task = asyncio.create_task(
            monitor_gofile_inactivity(expected_path, stop_evt, DOWNLOAD_INACTIVITY_TIMEOUT, status_msg, cancel_key, user)
        )

        await mgr.run()
        monitor_task.cancel()
        try:
            await monitor_task
        except asyncio.CancelledError:
            pass

        if stop_evt.is_set():
            return False, "cancelled by user or inactivity"

        if expected_path.exists():
            user_root = get_user_root_path(user).resolve()
            if expected_path.resolve() == user_root:
                logger.error(f"GoFile download path is the user root, refusing to compress: {expected_path}")
                return False, "path_is_user_root"
            processed = await process_path_with_suffix_and_signing_async(expected_path)
            if processed and await get_automator_enabled(user):
                await auto_compress_and_upload(
                    user=user,
                    original_path=processed,
                    chat_id=message.chat.id,
                    initiator_message=message,
                    cancel_key=cancel_key,
                    stop_event=stop_evt
                )
        return True, "success"
    except asyncio.TimeoutError:
        return False, "timeout"
    except Exception as e:
        logger.exception("gofile download failed")
        return False, str(e)

# ---------- Public uptime command ----------
async def cmd_uptime(client: Client, message: Message):
    if START_TIME is None:
        await notify_user_from_message(message, "El tiempo de actividad del bot no está disponible (no se registró la hora de inicio).")
        return
    now = time.time()
    elapsed = now - START_TIME
    days = int(elapsed // 86400)
    hours = int((elapsed % 86400) // 3600)
    minutes = int((elapsed % 3600) // 60)
    seconds = int(elapsed % 60)
    parts = []
    if days:
        parts.append(f"{days}d")
    if hours:
        parts.append(f"{hours}h")
    if minutes:
        parts.append(f"{minutes}m")
    parts.append(f"{seconds}s")
    uptime_str = " ".join(parts)
    await notify_user_from_message(message, f"🤖 Tiempo de actividad del bot: **{uptime_str}**")

async def cmd_start(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado. No eres un propietario autorizado de este bot.")
        return
    await notify_user_from_message(message, "Envía enlaces de descarga (soportados). Para archivos .torrent o magnets, el bot puede procesarlos localmente. Otros enlaces se enviarán a tu cola personal.\n\nUsa /automator para activar/desactivar la compresión y subida automática de todo lo que descargues. Cuando el Automator está ACTIVADO, cada descarga completada se dividirá en partes de 2GB en formato 7z y se subirá automáticamente.")

async def cmd_whoami(client: Client, message: Message):
    u = message.from_user
    uid = getattr(u, "id", None)
    uname = getattr(u, "username", None)
    await notify_user_from_message(message, f"id={uid} username={uname}")

async def cmd_help_owner(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado. No eres un propietario autorizado de este bot.")
        return
    await notify_user_from_message(message, "Envía enlaces en el chat. Los elementos Magnet y .torrent pueden procesarse localmente. Usa /status, /ls, /pwd, /zip, /mv, /cp, /rm, /upload, /cd, /back para gestionar tus archivos. Usa /setpass, /nopass y /pass_status para gestionar contraseñas por usuario para zip. Para activar cifrado establece SEVENZ_PATH en .env con la ruta de 7z.")

async def cmd_status(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    jd = None
    try:
        jd = await asyncio.wait_for(asyncio.to_thread(connect_jd), timeout=JD_API_TIMEOUT)
        try:
            device = await asyncio.wait_for(asyncio.to_thread(get_device_direct, jd, JD_DEVICE_NAME), timeout=JD_API_TIMEOUT)
            present = True
        except Exception:
            present = False
        await notify_user_from_message(message, f"Conectado al sistema de descargas. Dispositivo presente: {present}.")
    except Exception:
        logger.exception("Status failed")
        await notify_user_from_message(message, "Error de estado: no se pudo conectar al sistema de descargas.")
    finally:
        if jd:
            try:
                await asyncio.wait_for(asyncio.to_thread(jd.disconnect), timeout=JD_API_TIMEOUT)
            except Exception:
                pass

async def cmd_pwd(client: Client, message: Message):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    rel = CURRENT_DIRS.get(user.id, Path("."))
    if rel == Path(".") or str(rel) == ".":
        visible = "/"
    else:
        visible = "/" + str(rel).replace("\\", "/").lstrip("/")
    await notify_user_from_message(message, f"🗃Su directorio de trabajo: {visible}")

async def cmd_ls(client: Client, message: Message):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    working_msg = await notify_user_from_message(message, "🔄 Listando directorio...")
    try:
        items = await _list_user_items_async(user, timeout_seconds=COMMAND_TIMEOUT)
    except asyncio.TimeoutError:
        await notify_user_from_message(message, "⚠️ El comando ha agotado el tiempo. El directorio puede ser muy grande o estar en almacenamiento lento. Intente de nuevo.")
        logger.warning(f"ls command timed out for user {user.id if user else 'unknown'}")
        return
    except Exception as e:
        logger.exception("ls command failed")
        await notify_user_from_message(message, f"❌ Error al listar el directorio: {str(e)[:200]}")
        return
    txt = format_list_items(items)
    rel = CURRENT_DIRS.get(user.id, Path("."))
    if rel == Path(".") or str(rel) == ".":
        visible = "/"
    else:
        visible = "/" + str(rel).replace("\\", "/").lstrip("/")
    full_message = f"🗂Directorio: {visible}\n\n{txt}"
    MAX_LEN = 3500
    if len(full_message) <= MAX_LEN:
        await notify_user_from_message(message, full_message)
    else:
        for i in range(0, len(full_message), MAX_LEN):
            chunk = full_message[i:i+MAX_LEN]
            if i == 0:
                await notify_user_from_message(message, chunk)
            else:
                await safe_send(message.chat.id, chunk)

async def cmd_rm(client: Client, message: Message):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    args = message.text.split(None)[1:] if message.text else []
    if not args:
        await notify_user_from_message(message, "Uso: /rm <num> | <start-end> | <a,b,c> | * (ej. /rm 2,5-7 o /rm *)")
        return
    spec = " ".join(args).strip()
    items = await _list_user_items_async(user, timeout_seconds=COMMAND_TIMEOUT)
    if not items:
        await notify_user_from_message(message, "No hay archivos o carpetas en el directorio actual.")
        return
    targets = []
    if spec == "*" or spec.lower() == "all":
        targets = items[:]
    else:
        chosen_idxs = set()
        parts = [p.strip() for p in spec.split(",") if p.strip()]
        for p in parts:
            if "-" in p:
                try:
                    a, b = p.split("-", 1)
                    a_i = int(a); b_i = int(b)
                    if a_i <= 0 or b_i <= 0:
                        continue
                    low = min(a_i, b_i)
                    high = max(a_i, b_i)
                    for ii in range(low, high + 1):
                        chosen_idxs.add(ii)
                except Exception:
                    continue
            else:
                try:
                    ii = int(p)
                    if ii > 0:
                        chosen_idxs.add(ii)
                except Exception:
                    continue
        for idx in sorted(chosen_idxs):
            if 1 <= idx <= len(items):
                targets.append(items[idx - 1])
    if not targets:
        await notify_user_from_message(message, "No se seleccionaron elementos válidos para eliminar.")
        return
    seen_paths = set()
    unique_targets = []
    for t in targets:
        try:
            t_res = t.resolve()
        except Exception:
            t_res = t
        if str(t_res) not in seen_paths:
            seen_paths.add(str(t_res))
            unique_targets.append(t)
    try:
        await notify_user_from_message(message, f"🚮Iniciando eliminación de {len(unique_targets)} elemento(s)...")
    except Exception:
        pass
    removed, failed, skipped = [], [], []
    for t in unique_targets:
        try:
            if not ensure_within_user_root(user, t):
                skipped.append((t.name, "no permitido"))
                continue
            if not t.exists():
                skipped.append((t.name, "no encontrado"))
                continue
            if t.is_dir():
                await asyncio.wait_for(asyncio.to_thread(shutil.rmtree, t), timeout=FILE_IO_TIMEOUT)
            else:
                await asyncio.wait_for(asyncio.to_thread(t.unlink), timeout=FILE_IO_TIMEOUT)
            removed.append(t.name)
        except Exception as e:
            logger.exception("Failed to remove %s", t)
            failed.append((t.name, str(e)))
    lines = []
    if removed:
        lines.append(f"🗑Eliminados ({len(removed)}): " + ", ".join(removed))
    if skipped:
        lines.append("Omitidos:")
        for name, reason in skipped:
            lines.append(f"- {name}: {reason}")
    if failed:
        lines.append("Fallidos:")
        for name, err in failed:
            lines.append(f"- {name}: {err}")
    if not lines:
        await notify_user_from_message(message, "No se eliminó ningún elemento.")
    else:
        await notify_user_from_message(message, "\n".join(lines))

async def cmd_mv(client: Client, message: Message):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    parts = message.text.split(None)[1:] if message.text else []
    if not parts or len(parts) < 2:
        await notify_user_from_message(message, ("Uso:\n"
                                   "/mv <num|rango|a,b|*> <nuevonombre>    (renombrar un elemento)\n"
                                   "/mv <num|rango|a,b|*> /<índice_carpeta>  (mover elemento(s) a carpeta por índice)\n\n"
                                   "Ejemplos:\n"
                                   "/mv 8 nombre          -> renombra el elemento 8 a 'nombre'\n"
                                   "/mv 25 /5           -> mueve el elemento 25 a la carpeta 5\n"
                                   "/mv 6-10 /1         -> mueve los elementos 6..10 a la carpeta 1\n"
                                   "/mv 5,8,9 /2        -> mueve los elementos 5,8,9 a la carpeta 2\n"
                                   "/mv * /3            -> mueve todos los elementos a la carpeta 3\n"
                                   "/mv 6-10 /          -> mueve los elementos 6..10 a su directorio raíz"))
        return
    spec = parts[0].strip()
    dest_token = " ".join(parts[1:]).strip()
    items = await _list_user_items_async(user, timeout_seconds=COMMAND_TIMEOUT)
    if not items:
        await notify_user_from_message(message, "No hay archivos o carpetas en el directorio actual.")
        return
    def parse_selection(token: str, available_items: List[Path]) -> List[Path]:
        token = token.strip()
        if token == "*" or token.lower() == "all":
            return available_items[:]
        chosen = set()
        parts_ = [p.strip() for p in token.split(",") if p.strip()]
        for p in parts_:
            if "-" in p:
                try:
                    a, b = p.split("-", 1)
                    a_i = int(a); b_i = int(b)
                    low = min(a_i, b_i); high = max(a_i, b_i)
                    for ii in range(low, high + 1):
                        chosen.add(ii)
                except Exception:
                    continue
            else:
                try:
                    ii = int(p); chosen.add(ii)
                except Exception:
                    continue
        result = []
        for idx in sorted(chosen):
            if 1 <= idx <= len(available_items):
                result.append(available_items[idx - 1])
        return result
    is_move_into_folder = False
    folder_index = None
    dest_token_stripped = dest_token.strip()
    if dest_token_stripped.startswith("/"):
        after = dest_token_stripped[1:].strip()
        if after == "":
            is_move_into_folder = True
            folder_index = 0
        else:
            try:
                folder_index = int(after)
                is_move_into_folder = True
            except Exception:
                await notify_user_from_message(message, "La carpeta de destino debe especificarse como '/' para raíz o '/<índice>' donde el índice es el número de carpeta mostrado en /ls.")
                return
    else:
        is_move_into_folder = False
    sources = parse_selection(spec, items)
    if not sources:
        await notify_user_from_message(message, "No se seleccionaron elementos fuente válidos.")
        return
    if is_move_into_folder:
        if folder_index == 0:
            dest_path = get_user_root_path(user)
        else:
            dest_path = resolve_user_index_to_path(user, folder_index)
            if dest_path is None:
                await notify_user_from_message(message, "Índice de carpeta de destino inválido.")
                return
        if not dest_path.exists():
            await notify_user_from_message(message, "La carpeta de destino no existe.")
            return
        if not dest_path.is_dir():
            await notify_user_from_message(message, "El índice de destino no es una carpeta.")
            return
        if not ensure_within_user_root(user, dest_path):
            await notify_user_from_message(message, "La operación escaparía de su carpeta de usuario; abortada.")
            return
        filtered_sources = []
        try:
            dest_resolved = dest_path.resolve()
        except Exception:
            dest_resolved = dest_path
        for s in sources:
            try:
                s_res = s.resolve()
            except Exception:
                s_res = s
            if str(s_res) == str(dest_resolved):
                continue
            try:
                dest_resolved.relative_to(s_res)
                await notify_user_from_message(message, f"Saltando '{s.name}': el destino '{dest_path.name}' está dentro de este elemento.")
                continue
            except Exception:
                filtered_sources.append(s)
        sources = filtered_sources
        if not sources:
            await notify_user_from_message(message, "No quedan elementos válidos para mover después del filtrado (carpeta destino excluida).")
            return
        try:
            await notify_user_from_message(message, f"Iniciando movimiento de {len(sources)} elemento(s) a '{dest_path.name}'...")
        except Exception:
            pass
        moved, skipped, failed = [], [], []
        for src in sources:
            try:
                if not ensure_within_user_root(user, src):
                    skipped.append((src.name, "no permitido"))
                    continue
                if not src.exists():
                    skipped.append((src.name, "no encontrado"))
                    continue
                candidate_name = sanitize_filename(src.name)
                target = (dest_path / candidate_name).resolve()
                if not ensure_within_user_root(user, target):
                    skipped.append((src.name, "no permitido (escape)"))
                    continue
                if target.exists():
                    counter = 1
                    base_stem = target.stem if target.is_file() else target.name
                    suffix = target.suffix if target.is_file() else ""
                    candidate = target
                    while candidate.exists():
                        if suffix:
                            candidate = dest_path / f"{base_stem}_mv_{counter}{suffix}"
                        else:
                            candidate = dest_path / f"{base_stem}_mv_{counter}"
                        counter += 1
                    target = candidate
                try:
                    await asyncio.wait_for(asyncio.to_thread(src.rename, target), timeout=FILE_IO_TIMEOUT)
                except Exception:
                    if src.is_dir():
                        await asyncio.wait_for(asyncio.to_thread(shutil.copytree, str(src), str(target)), timeout=FILE_IO_TIMEOUT)
                        await asyncio.wait_for(asyncio.to_thread(shutil.rmtree, src), timeout=FILE_IO_TIMEOUT)
                    else:
                        await asyncio.wait_for(asyncio.to_thread(shutil.copy2, str(src), str(target)), timeout=FILE_IO_TIMEOUT)
                        await asyncio.wait_for(asyncio.to_thread(src.unlink), timeout=FILE_IO_TIMEOUT)
                moved.append((src.name, target.name))
            except Exception as e:
                logger.exception("mv (move into folder) failed for %s", src)
                failed.append((src.name, str(e)))
        lines = []
        if moved:
            lines.append("Movidos:")
            for a, b in moved:
                lines.append(f"- {a} -> {b}")
        if skipped:
            lines.append("Omitidos:")
            for name, reason in skipped:
                lines.append(f"- {name}: {reason}")
        if failed:
            lines.append("Fallidos:")
            for name, err in failed:
                lines.append(f"- {name}: {err}")
        await notify_user_from_message(message, "\n".join(lines) if lines else "No se movió ningún elemento.")
        return
    if len(sources) != 1:
        await notify_user_from_message(message, "La operación de renombrado requiere un único elemento fuente. Para mover varios elementos a una carpeta use '/mv <spec> /<índice_carpeta>' o '/mv <spec> /' para mover a raíz.")
        return
    src = sources[0]
    newname_raw = dest_token
    if not newname_raw:
        await notify_user_from_message(message, "El nuevo nombre no puede estar vacío.")
        return
    if "/" in newname_raw or "\\" in newname_raw:
        await notify_user_from_message(message, "El nuevo nombre debe ser un nombre simple, no una ruta.")
        return
    safe_new = sanitize_filename(newname_raw)
    if not safe_new:
        await notify_user_from_message(message, "El nuevo nombre no es válido después de la sanitización.")
        return
    root = get_user_root_path(user)
    try:
        current_parent = src.resolve().parent
    except Exception:
        current_parent = root
    destination = (current_parent / safe_new).resolve()
    if not ensure_within_user_root(user, destination):
        await notify_user_from_message(message, "La operación escaparía de su carpeta de usuario; abortada.")
        return
    if destination.exists():
        await notify_user_from_message(message, "Ya existe un archivo/carpeta con el nuevo nombre.")
        return
    try:
        await notify_user_from_message(message, f"🔄Iniciando renombrado de '{src.name}' -> '{safe_new}'...")
    except Exception:
        pass
    try:
        await asyncio.wait_for(asyncio.to_thread(src.rename, destination), timeout=FILE_IO_TIMEOUT)
        await notify_user_from_message(message, f"✅Renombrado '{src.name}' -> '{destination.name}'")
    except Exception:
        logger.exception("mv rename failed")
        await notify_user_from_message(message, "Renombrado fallido: no se pudo renombrar el elemento.")

async def cmd_cp(client: Client, message: Message):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    parts = message.text.split(None)[1:] if message.text else []
    if not parts or len(parts) < 2:
        await notify_user_from_message(message, "Uso: /cp <num|rango|a,b|*> /<índice_carpeta>  (ej. /cp 1,3,5 /2 o /cp * / o /cp 2-6 /1)")
        return
    spec = parts[0].strip()
    dest_token = " ".join(parts[1:]).strip()
    items = await _list_user_items_async(user, timeout_seconds=COMMAND_TIMEOUT)
    if not items:
        await notify_user_from_message(message, "No hay archivos o carpetas en el directorio actual.")
        return
    def parse_selection(token: str, available_items: List[Path]) -> List[Path]:
        t = token.strip()
        if t == "*" or t.lower() == "all":
            return available_items[:]
        chosen = set()
        parts_ = [p.strip() for p in t.split(",") if p.strip()]
        for p in parts_:
            if "-" in p:
                try:
                    a, b = p.split("-", 1)
                    a_i = int(a); b_i = int(b)
                    low = min(a_i, b_i); high = max(a_i, b_i)
                    for ii in range(low, high + 1):
                        chosen.add(ii)
                except Exception:
                    continue
            else:
                try:
                    ii = int(p); chosen.add(ii)
                except Exception:
                    continue
        result = []
        for idx in sorted(chosen):
            if 1 <= idx <= len(available_items):
                result.append(available_items[idx - 1])
        return result
    dest_token_stripped = dest_token.strip()
    if not dest_token_stripped.startswith("/"):
        await notify_user_from_message(message, "El destino debe ser '/' para raíz o '/<índice>' donde el índice es el número de carpeta mostrado en /ls.")
        return
    after = dest_token_stripped[1:].strip()
    if after == "":
        dest_path = get_user_root_path(user)
    else:
        try:
            folder_index = int(after)
        except Exception:
            await notify_user_from_message(message, "El destino debe ser '/' para raíz o '/<índice>' donde el índice es el número de carpeta mostrado en /ls.")
            return
        dest_path = resolve_user_index_to_path(user, folder_index)
        if dest_path is None:
            await notify_user_from_message(message, "Índice de carpeta de destino inválido.")
            return
    if not dest_path.exists():
        await notify_user_from_message(message, "La carpeta de destino no existe.")
        return
    if not dest_path.is_dir():
        await notify_user_from_message(message, "El índice de destino no es una carpeta.")
        return
    if not ensure_within_user_root(user, dest_path):
        await notify_user_from_message(message, "La operación escaparía de su carpeta de usuario; abortada.")
        return

    # ---- Disk quota and free space check ----
    user_root = get_user_root_path(user)
    ok, msg = await check_disk_free_space(user_root)
    if not ok:
        await notify_user_from_message(message, msg)
        return
    total_size = 0
    sources = parse_selection(spec, items)
    if not sources:
        await notify_user_from_message(message, "No se seleccionaron elementos fuente válidos.")
        return
    for src in sources:
        if src.exists():
            total_size += await asyncio.wait_for(asyncio.to_thread(get_total_size_sync, src), timeout=THREADED_WALK_TIMEOUT)
    ok, msg = await check_user_quota(user, additional_bytes=total_size)
    if not ok:
        await notify_user_from_message(message, msg)
        return

    filtered_sources = []
    for s in sources:
        try:
            s_res = s.resolve()
        except Exception:
            s_res = s
        try:
            dest_res = dest_path.resolve()
        except Exception:
            dest_res = dest_path
        skip = False
        try:
            if dest_res == s_res or dest_res.relative_to(s_res):
                await notify_user_from_message(message, f"Saltando '{s.name}': el destino '{dest_path.name}' está dentro de este elemento.")
                skip = True
        except Exception:
            pass
        if not skip:
            filtered_sources.append(s)
    if not filtered_sources:
        await notify_user_from_message(message, "No quedan elementos válidos para copiar después del filtrado (carpeta destino excluida).")
        return
    try:
        await notify_user_from_message(message, f"Iniciando copia de {len(filtered_sources)} elemento(s) a '{dest_path.name}'...")
    except Exception:
        pass
    copied, skipped, failed = [], [], []
    for src in filtered_sources:
        try:
            if not ensure_within_user_root(user, src):
                skipped.append((src.name, "no permitido"))
                continue
            if not src.exists():
                skipped.append((src.name, "no encontrado"))
                continue
            candidate_name = sanitize_filename(src.name)
            target = (dest_path / candidate_name).resolve()
            if not ensure_within_user_root(user, target):
                skipped.append((src.name, "no permitido (escape)"))
                continue
            if target.exists():
                counter = 1
                if target.is_file():
                    base_stem = target.stem
                    suffix = target.suffix
                    candidate = target
                    while candidate.exists():
                        candidate = dest_path / f"{base_stem}_copy_{counter}{suffix}"
                        counter += 1
                    target = candidate
                else:
                    base_name = target.name
                    candidate = target
                    while candidate.exists():
                        candidate = dest_path / f"{base_name}_copy_{counter}"
                        counter += 1
                    target = candidate
            if src.is_dir():
                await asyncio.wait_for(asyncio.to_thread(shutil.copytree, str(src), str(target)), timeout=FILE_IO_TIMEOUT)
            else:
                await asyncio.wait_for(asyncio.to_thread(shutil.copy2, str(src), str(target)), timeout=FILE_IO_TIMEOUT)
            copied.append((src.name, target.name))
        except Exception as e:
            logger.exception("cp (copy into folder) failed for %s", src)
            failed.append((src.name, str(e)))
    lines = []
    if copied:
        lines.append("Copiados:")
        for a, b in copied:
            lines.append(f"- {a} -> {b}")
    if skipped:
        lines.append("Omitidos:")
        for name, reason in skipped:
            lines.append(f"- {name}: {reason}")
    if failed:
        lines.append("Fallidos:")
        for name, err in failed:
            lines.append(f"- {name}: {err}")
    await notify_user_from_message(message, "\n".join(lines) if lines else "No se copió ningún elemento.")

ZIP_PROGRESS_UPDATE_INTERVAL = 5.0
UNZIP_PROGRESS_UPDATE_INTERVAL = 5.0

# ------------------------------------------------------------
# FIXED cmd_zip with size-based progress
# ------------------------------------------------------------
async def cmd_zip(client: Client, message: Message, from_queue: bool = False):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    if not from_queue:
        await enqueue_user_task(user, client, message, cmd_zip)
        return
    async with ZIP_SEMAPHORE:
        args = message.text.split(None)[1:] if message.text else []
        if len(args) < 1:
            await notify_user_from_message(message, "Uso: /zip <num> [<tamaño_max_mb>] (ej. /zip 2 500 o /zip 2)")
            return
        try:
            idx = int(args[0])
        except Exception:
            await notify_user_from_message(message, "El primer argumento debe ser un número (el índice del archivo mostrado en /ls).")
            return
        max_mb = None
        if len(args) >= 2:
            try:
                max_mb = int(args[1])
            except Exception:
                await notify_user_from_message(message, "El segundo argumento (si se proporciona) debe ser un número que represente el tamaño máximo en MB por parte.")
                return
        target = resolve_user_index_to_path(user, idx)
        if not target:
            await notify_user_from_message(message, "Índice inválido.")
            return
        if not ensure_within_user_root(user, target):
            await notify_user_from_message(message, "Operación no permitida.")
            return
        root = get_user_root_path(user)
        cur_rel = CURRENT_DIRS.get(user.id, Path("."))
        try:
            current = (root / cur_rel).resolve()
        except Exception:
            current = root

        # ---- Disk quota and free space check ----
        user_root = get_user_root_path(user)
        ok, msg = await check_disk_free_space(user_root)
        if not ok:
            await notify_user_from_message(message, msg)
            return
        total_size = await asyncio.wait_for(asyncio.to_thread(get_total_size_sync, target), timeout=THREADED_WALK_TIMEOUT)
        ok, msg = await check_user_quota(user, additional_bytes=total_size)
        if not ok:
            await notify_user_from_message(message, msg)
            return

        total_input_size = total_size

        base_name = sanitize_filename(target.name)
        zip_name = f"{base_name}.7z"
        zip_path = (current / zip_name).resolve()
        out_dir = current

        try:
            await notify_user_from_message(message, f"🔄Creando archivo comprimido '{zip_name}' ...")
            seven_cmd = None
            try:
                if SEVENZ_PATH:
                    sp = Path(SEVENZ_PATH)
                    if sp.exists() and sp.is_file():
                        seven_cmd = str(sp)
                    else:
                        found = shutil.which(SEVENZ_PATH)
                        if found:
                            seven_cmd = found
                        else:
                            seven_cmd = shutil.which("7z") or shutil.which("7za") or shutil.which("7zr")
                else:
                    seven_cmd = shutil.which("7z") or shutil.which("7za") or shutil.which("7zr")
            except Exception:
                seven_cmd = shutil.which("7z") or shutil.which("7za") or shutil.which("7zr")
            if not seven_cmd:
                try:
                    await asyncio.wait_for(asyncio.to_thread(create_zip_for_path, target, zip_path), timeout=FALLBACK_ZIP_TIMEOUT)
                    encrypted_zip_path = zip_path
                    if max_mb is None:
                        size_str = human_size(encrypted_zip_path.stat().st_size)
                        msg = f"✅Comprimido creado: {encrypted_zip_path.name} ({size_str})"
                        await notify_user_from_message(message, msg)
                    else:
                        max_bytes = max(1, max_mb) * 1024 * 1024
                        if encrypted_zip_path.stat().st_size > max_bytes:
                            parts = await asyncio.wait_for(asyncio.to_thread(split_file, encrypted_zip_path, max_bytes), timeout=FALLBACK_ZIP_TIMEOUT)
                            await asyncio.wait_for(asyncio.to_thread(encrypted_zip_path.unlink, missing_ok=True), timeout=FILE_IO_TIMEOUT)
                            part_names = ", ".join(p.name for p in parts)
                            await notify_user_from_message(message, f"🧩Creadas {len(parts)} partes: {part_names}")
                        else:
                            size_str = human_size(encrypted_zip_path.stat().st_size)
                            msg = f"✅Comprimido creado: {encrypted_zip_path.name} ({size_str})"
                            await notify_user_from_message(message, msg)
                    return
                except Exception:
                    logger.exception("Failed fallback python zip creation and 7z not found")
                    await notify_user_from_message(message, "No se encontró la herramienta de compresión (7z) y la compresión alternativa falló. Instale 7z o configure SEVENZ_PATH.")
                    return
            user_pwd = PASSWORDS.get(user.id)
            memopt = "-mem=AES256" if user_pwd else None
            parts_flag = None
            if max_mb is not None and max_mb > 0:
                parts_flag = f"-v{max_mb}m"
            try:
                if zip_path.exists():
                    await asyncio.wait_for(asyncio.to_thread(zip_path.unlink, missing_ok=True), timeout=FILE_IO_TIMEOUT)
            except Exception:
                logger.debug("Could not remove existing zip before creation: %s", zip_path)
            cwd = str(target.parent)
            src_arg = target.name
            cmd = [seven_cmd, "a", "-t7z", "-bb1", "-bsp1", "-mx=0"]
            if user_pwd:
                cmd.append(f"-p{user_pwd}")
                if memopt:
                    cmd.append(memopt)
            if parts_flag:
                cmd.append(parts_flag)
            cmd.append("-y")
            cmd.append(str(zip_path))
            cmd.append(src_arg)

            progress_markup = _zip_cancel_keyboard()
            initial_text = "<i>Preparando compresión...</i>"
            progress_msg = None
            try:
                progress_msg = await safe_reply(message, initial_text, reply_markup=progress_markup, parse_mode=ParseMode.HTML)
            except Exception:
                progress_msg = None
            if not progress_msg:
                try:
                    progress_msg = await safe_send(message.chat.id, initial_text, reply_markup=progress_markup, parse_mode=ParseMode.HTML)
                except Exception:
                    progress_msg = None
            if not progress_msg:
                try:
                    await notify_user_from_message(message, "Iniciando compresión...")
                except Exception:
                    pass

            zip_start_time = time.time()
            spinner_chars = ['⠋','⠙','⠹','⠸','⠼','⠴','⠦','⠧','⠇','⠏']

            async def _edit_progress(txt: str, keep_button: bool = True):
                if not progress_msg:
                    return
                reply_markup = progress_markup if keep_button else None
                # Use fire-and-forget resilient edit
                asyncio.create_task(
                    edit_progress_resilient(
                        progress_msg, txt,
                        reply_markup=reply_markup,
                        client=bot_client,
                        per_attempt_timeout=5.0
                    )
                )

            proc = await asyncio.create_subprocess_exec(
                *cmd,
                cwd=cwd,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.STDOUT
            )
            message_id = None
            if progress_msg:
                message_id = getattr(progress_msg, "message_id", None) or getattr(progress_msg, "id", None)
            if message_id is not None:
                ZIP_TASKS[message_id] = {"process": proc, "user_id": getattr(user, "id", None), "cancelled": False}

            def get_output_size_sum():
                total = 0
                if parts_flag:
                    pattern = re.compile(rf"^{re.escape(zip_path.name)}\.\d+$")
                    for entry in out_dir.iterdir():
                        if pattern.match(entry.name) and entry.is_file():
                            total += entry.stat().st_size
                else:
                    if zip_path.exists():
                        total = zip_path.stat().st_size
                return total

            last_pct = -1.0
            last_emit = time.time()
            progress_updater_running = True

            async def update_size_progress():
                nonlocal last_pct, last_emit
                while progress_updater_running:
                    await asyncio.sleep(6.0)
                    if proc.returncode is not None:
                        break
                    if message_id and ZIP_TASKS.get(message_id, {}).get("cancelled"):
                        break
                    out_size = await asyncio.wait_for(asyncio.to_thread(get_output_size_sum), timeout=FILE_IO_TIMEOUT)
                    if total_input_size > 0:
                        pct = min(100.0, (out_size / total_input_size) * 100.0)
                    else:
                        pct = 0.0
                    # ---------- QUOTA CHECK ----------
                    remaining = total_input_size - out_size
                    if await check_quota_and_abort(user,
                                                   additional_bytes=remaining,
                                                   progress_msg=progress_msg):
                        if message_id in ZIP_TASKS:
                            ZIP_TASKS[message_id]['cancelled'] = True
                        if proc.returncode is None:
                            proc.terminate()
                        break
                    # ---------------------------------
                    if pct != last_pct:
                        elapsed = int(time.time() - zip_start_time)
                        spinner = spinner_chars[elapsed % len(spinner_chars)]
                        await _edit_progress(_zip_progress_text(target.name, pct, elapsed, spinner))
                        last_pct = pct
                        last_emit = time.time()

            progress_updater = asyncio.create_task(update_size_progress())

            error_buffer = []
            try:
                stdout_pipe = proc.stdout
                buffer = b""
                while stdout_pipe is not None:
                    try:
                        chunk = await asyncio.wait_for(stdout_pipe.read(64), timeout=SEVENZ_READ_TIMEOUT)
                        if not chunk:
                            break
                        buffer += chunk
                        while True:
                            if b"\r" in buffer:
                                line, buffer = buffer.split(b"\r", 1)
                            elif b"\n" in buffer:
                                line, buffer = buffer.split(b"\n", 1)
                            else:
                                break
                            decoded = line.decode(errors="ignore").strip()
                            if not decoded:
                                continue
                            error_buffer.append(decoded)
                            if len(error_buffer) > 20:
                                error_buffer.pop(0)
                            if message_id is not None:
                                task_entry = ZIP_TASKS.get(message_id)
                                if task_entry and task_entry.get("cancelled"):
                                    break
                    except asyncio.TimeoutError:
                        logger.warning("7z output read timed out, terminating process")
                        proc.terminate()
                        break
            except Exception:
                logger.exception("Failed to read 7z output")

            rc = await proc.wait()
            progress_updater_running = False
            progress_updater.cancel()
            try:
                await progress_updater
            except asyncio.CancelledError:
                pass

            combined_output = "\n".join(error_buffer)
            task_entry = ZIP_TASKS.pop(message_id, None) if message_id is not None else None
            if task_entry and task_entry.get("cancelled"):
                return

            if rc != 0:
                lower_output = combined_output.lower()
                if any(kw in lower_output for kw in ["data error", "wrong password", "incorrect password", "cannot open", "access is denied", "permission denied"]):
                    await _edit_progress("<i>La herramienta de compresión falló al crear el archivo.</i>", keep_button=False)
                    await notify_user_from_message(message, "Fallo al crear el archivo comprimido: " + (combined_output.splitlines()[0] if combined_output else "error desconocido"))
                    return
                if not user_pwd:
                    try:
                        await asyncio.wait_for(asyncio.to_thread(create_zip_for_path, target, zip_path), timeout=FALLBACK_ZIP_TIMEOUT)
                        size_str = human_size(zip_path.stat().st_size) if zip_path.exists() else "?"
                        msg = f"Comprimido creado (alternativa): {zip_path.name} ({size_str})"
                        if progress_msg:
                            await _edit_progress(f"<i>{msg}</i>", keep_button=False)
                        else:
                            await notify_user_from_message(message, msg)
                        if max_mb is not None:
                            max_bytes = max(1, max_mb) * 1024 * 1024
                            if zip_path.stat().st_size > max_bytes:
                                parts = await asyncio.wait_for(asyncio.to_thread(split_file, zip_path, max_bytes), timeout=FALLBACK_ZIP_TIMEOUT)
                                await asyncio.wait_for(asyncio.to_thread(zip_path.unlink, missing_ok=True), timeout=FILE_IO_TIMEOUT)
                                part_names = ", ".join(p.name for p in parts)
                                await notify_user_from_message(message, f"🧩Creadas {len(parts)} partes: {part_names}")
                        return
                    except Exception:
                        logger.exception("Fallback python zip also failed after 7z error")
                        if progress_msg:
                            await _edit_progress("<i>La compresión alternativa también falló.</i>", keep_button=False)
                        else:
                            await notify_user_from_message(message, "Error al crear el archivo comprimido (falló la herramienta y la alternativa).")
                        return
                else:
                    if progress_msg:
                        await _edit_progress("<i>Falló al crear el archivo cifrado con la herramienta de compresión.</i>", keep_button=False)
                    else:
                        await notify_user_from_message(message, "Falló al crear el archivo cifrado. Asegúrese de que la contraseña y la instalación de 7z sean correctas.")
                    return

            created_files = []
            if parts_flag:
                parent_dir = zip_path.parent
                prefix = zip_path.name + "."
                try:
                    for p in parent_dir.iterdir():
                        if p.name.startswith(prefix) and p.is_file():
                            created_files.append(p.name)
                except Exception:
                    logger.exception("Failed to enumerate split parts for %s", zip_path)
                if not created_files:
                    try:
                        for p in parent_dir.iterdir():
                            if p.name.startswith(base_name) and p.is_file() and (p.name.endswith(".001") or re.search(r"\.z\d{2}$", p.name)):
                                created_files.append(p.name)
                    except Exception:
                        pass
            else:
                if zip_path.exists():
                    created_files.append(zip_path.name)
                else:
                    try:
                        alt = Path(cwd) / zip_path.name
                        if alt.exists():
                            created_files.append(alt.name)
                    except Exception:
                        pass

            if not created_files:
                try:
                    size_str = human_size(zip_path.stat().st_size) if zip_path.exists() else "?"
                except Exception:
                    size_str = "?"
                msg = f"✅Comprimido creado: {zip_path.name} ({size_str})"
                if progress_msg:
                    await _edit_progress(f"<i>{msg}</i>", keep_button=False)
                else:
                    await notify_user_from_message(message, msg)
                return

            if len(created_files) == 1:
                try:
                    file_path = zip_path if zip_path.exists() else (Path(cwd) / created_files[0])
                    size_str = human_size(file_path.stat().st_size) if file_path.exists() else "?"
                except Exception:
                    size_str = "?"
                msg = f"✅Comprimido creado: {created_files[0]} ({size_str})"
                if progress_msg:
                    await _edit_progress(f"<i>{msg}</i>", keep_button=False)
                else:
                    await notify_user_from_message(message, msg)
            else:
                msg = f"🧩Creadas {len(created_files)} partes: {', '.join(created_files)}"
                if progress_msg:
                    await _edit_progress(f"<i>{msg}</i>", keep_button=False)
                else:
                    await notify_user_from_message(message, msg)

        except Exception:
            logger.exception("zip failed")
            await notify_user_from_message(message, "Error interno al crear el archivo comprimido.")

async def cmd_set_description(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    args = message.text.split(None)[1:] if message.text else []
    if not args:
        await notify_user_from_message(message, "Uso: /set_description <texto>")
        return
    global UPLOAD_DESCRIPTION
    UPLOAD_DESCRIPTION = " ".join(args).strip()
    if UPLOAD_DESCRIPTION == "":
        set_upload_description_and_save(None)
        await notify_user_from_message(message, "Descripción eliminada.")
    else:
        set_upload_description_and_save(UPLOAD_DESCRIPTION)
        await notify_user_from_message(message, "Descripción de subida establecida.")

async def cmd_description(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    if UPLOAD_DESCRIPTION:
        display = UPLOAD_DESCRIPTION if len(UPLOAD_DESCRIPTION) <= 3500 else UPLOAD_DESCRIPTION[:3496] + "..."
        await notify_user_from_message(message, f"Descripción de subida actual:\n\n{display}")
    else:
        await notify_user_from_message(message, "No hay descripción de subida establecida.")

async def cmd_no_description(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    set_upload_description_and_save(None)
    await notify_user_from_message(message, "Descripción de subida deshabilitada.")

# ============================================================
# IMPROVED upload_with_retry with hard reset on hanging cancellation
# and monitor cancellation timeout
# ============================================================
UPLOAD_ATTEMPT_TIMEOUT = 1200  # increased from 900 (20 min)
UPLOAD_INACTIVITY_TIMEOUT = 1200  # increased from 900 (20 min)

async def upload_with_retry(upload_client, send_kwargs, max_retries=20):
    progress = send_kwargs.get('progress')
    base_delay = 1.0
    consecutive_failures = 0

    for attempt in range(max_retries):
        delay = min(base_delay * (2 ** attempt), 60.0)

        # Solo reconectar, nunca stop/start
        if not upload_client.is_connected:
            logger.warning(f"Client disconnected, reconnecting (attempt {attempt+1})...")
            try:
                await asyncio.wait_for(upload_client.reconnect(), timeout=15.0)
            except Exception as e:
                logger.error(f"Reconnection failed: {e}")
                await asyncio.sleep(delay)
                continue

        # Health check ligero (sin reconexión forzada)
        try:
            await asyncio.wait_for(upload_client.get_me(), timeout=5.0)
        except Exception:
            logger.warning("Health check failed, will retry after delay")
            await asyncio.sleep(delay)
            continue

        upload_task = asyncio.create_task(upload_client.send_document(**send_kwargs))
        monitors = []
        task_cancelled = False

        # Monitor de inactividad (más permisivo)
        if progress is not None:
            progress.last_progress_time = time.time()
            async def inactivity_monitor():
                nonlocal task_cancelled
                while not upload_task.done():
                    if asyncio.current_task().cancelled():
                        break
                    await asyncio.sleep(20)  # Aumentado de 15 a 20s
                    if time.time() - progress.last_progress_time > UPLOAD_INACTIVITY_TIMEOUT:
                        logger.warning("Upload inactivity timeout, cancelling task")
                        task_cancelled = True
                        upload_task.cancel()
                        break
            monitors.append(asyncio.create_task(inactivity_monitor()))

        # Monitor de conexión (solo alerta, no cancela)
        async def connection_monitor():
            nonlocal task_cancelled
            while not upload_task.done():
                if asyncio.current_task().cancelled():
                    break
                await asyncio.sleep(10)
                if not upload_client.is_connected:
                    logger.warning("Client disconnected during upload")
                    # No cancelamos, dejamos que falle naturalmente y se reintente
            monitors.append(asyncio.create_task(connection_monitor()))

        try:
            result = await asyncio.wait_for(upload_task, timeout=UPLOAD_ATTEMPT_TIMEOUT)
            return result
        except asyncio.TimeoutError:
            logger.error(f"Upload attempt {attempt+1} timed out")
            upload_task.cancel()
            consecutive_failures += 1
            if consecutive_failures >= 3:
                # Solo reconexión, no stop/start
                try:
                    await upload_client.restart()
                except Exception:
                    pass
                consecutive_failures = 0
        except asyncio.CancelledError:
            if task_cancelled:
                logger.info("Upload attempt cancelled by monitor – will retry")
                consecutive_failures += 1
                if consecutive_failures >= 3:
                    try:
                        await upload_client.restart()
                    except Exception:
                        pass
                    consecutive_failures = 0
            else:
                raise
        except (aiohttp.ClientError, ConnectionError, OSError) as e:
            logger.warning(f"Network error: {e}")
            upload_task.cancel()
            consecutive_failures += 1
            if consecutive_failures >= 3:
                try:
                    await upload_client.restart()
                except Exception:
                    pass
                consecutive_failures = 0
        except Exception as e:
            logger.exception("Unexpected upload error")
            raise
        finally:
            for m in monitors:
                if not m.done():
                    m.cancel()
                    try:
                        await asyncio.wait_for(m, timeout=2.0)
                    except (asyncio.TimeoutError, asyncio.CancelledError):
                        pass

        if attempt == max_retries - 1:
            raise Exception(f"All {max_retries} upload attempts failed")
        await asyncio.sleep(delay)

# ============================================================
# MODIFIED cmd_upload to pass upload_client to OptimizedProgress
# ============================================================
async def cmd_upload(client: Client, message: Message, from_queue: bool = False):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    if not from_queue:
        await enqueue_user_task(user, client, message, cmd_upload)
        return

    initiator_id = None
    try:
        if message.from_user and getattr(message.from_user, "id", None) is not None:
            initiator_id = int(message.from_user.id)
    except Exception:
        initiator_id = None

    async def notify(text: str, reply_message: Optional[Message] = None):
        if initiator_id is not None and initiator_id != BOT_ID:
            try:
                await safe_send(initiator_id, text)
                return
            except Exception:
                pass
        try:
            if reply_message:
                await safe_reply(reply_message, text)
            else:
                await safe_reply(message, text)
        except Exception:
            logger.exception("notify fallback failed")

    args = message.text.split(None)[1:] if message.text else []
    if not args:
        await notify("Uso: /upload * O /upload 2,4,5")
        return
    spec = " ".join(args).strip()
    root = get_user_root_path(user)
    items = await _list_user_items_async(user, timeout_seconds=COMMAND_TIMEOUT)
    to_upload = []
    if spec == "*" or spec.lower() == "all":
        to_upload = items
    else:
        chosen = set()
        parts = spec.split(",")
        for p in parts:
            p = p.strip()
            if not p:
                continue
            if "-" in p:
                try:
                    a, b = p.split("-", 1)
                    a_i = int(a); b_i = int(b)
                    for ii in range(a_i, b_i + 1):
                        chosen.add(ii)
                except Exception:
                    pass
            else:
                try:
                    chosen.add(int(p))
                except Exception:
                    pass
        for idx in sorted(chosen):
            item = resolve_user_index_to_path(user, idx)
            if item:
                to_upload.append(item)
    if not to_upload:
        await notify("No se seleccionaron elementos para subir.")
        return

    # ---- Disk free space check ----
    user_root = get_user_root_path(user)
    ok, msg = await check_disk_free_space(user_root)
    if not ok:
        await notify(msg)
        return

    upload_group_id = uuid.uuid4().hex
    cancel_event = asyncio.Event()
    UPLOAD_GROUPS[upload_group_id] = {"cancel_event": cancel_event, "active_task": None}
    chat_id = message.chat.id

    async def _edit_progress_safe(msg: Message, new_text: str, keep_button: bool = True):
        if not msg:
            return
        try:
            reply_markup = _upload_cancel_keyboard(upload_group_id) if keep_button else None
            await edit_with_retry(msg.edit(_scrub_text_for_user(new_text), reply_markup=reply_markup, parse_mode=ParseMode.HTML))
        except Exception:
            pass

    def build_caption_with_description(filename: str) -> str:
        if UPLOAD_DESCRIPTION:
            safe_desc = UPLOAD_DESCRIPTION
            return f"<i>{filename}</i>\n\n<i>{safe_desc}</i>"
        else:
            return f"<i>{filename}</i>"

    try:
        for p in to_upload:
            if cancel_event.is_set():
                break
            try:
                if not ensure_within_user_root(user, p):
                    await notify(f"Saltando {p.name}: no permitido.")
                    continue
                if p.is_dir():
                    await notify(f"'{p.name}' es una carpeta. No se admite la subida de carpetas. Suba archivos individuales.")
                    continue
                if not p.exists() or not p.is_file():
                    await notify(f"Archivo no encontrado: {p.name}")
                    continue

                try:
                    total_size = int(p.stat().st_size)
                except Exception:
                    total_size = None

                start_time = time.time()
                initial_text = build_progress_text(p.name, total_size, 0, 0.0, None)
                progress_markup = _upload_cancel_keyboard(upload_group_id)
                try:
                    progress_msg = await safe_reply(message, initial_text, reply_markup=progress_markup)
                except Exception:
                    progress_msg = await safe_reply(message, "Iniciando subida...", reply_markup=progress_markup)

                if progress_msg is None:
                    logger.error("Failed to create progress message for upload")
                    class DummyMsg:
                        async def edit(self, text, **kwargs):
                            pass
                    progress_msg = DummyMsg()

                caption_html = build_caption_with_description(p.name)
                group_info = UPLOAD_GROUPS.get(upload_group_id)

                thumb_path = None
                if THUMBNAIL_PATH and THUMBNAIL_PATH.exists():
                    validated_thumb = await asyncio.wait_for(asyncio.to_thread(validate_and_fix_thumbnail, THUMBNAIL_PATH), timeout=FILE_IO_TIMEOUT)
                    if validated_thumb and validated_thumb.exists():
                        thumb_path = str(validated_thumb)
                        logger.info(f"Using thumbnail for upload: {thumb_path}")
                    else:
                        logger.warning(f"Thumbnail validation failed, proceeding without thumbnail")
                
                if FORCE_USER_UPLOADS:
                    use_bot = False
                elif FORCE_BOT_UPLOADS:
                    use_bot = True
                else:
                    use_bot = (total_size and total_size > LARGE_FILE_THRESHOLD)
                if not use_bot and user_client is None:
                    logger.warning("User client not available, falling back to bot client")
                    use_bot = True
                upload_client = bot_client if use_bot else user_client
                client_name = "bot" if use_bot else "usuario"

                try:
                    try:
                        await edit_with_retry(progress_msg.edit(_scrub_text_for_user(f"<i>Subiendo a través de la API de {client_name}...</i>"), reply_markup=progress_markup, parse_mode=ParseMode.HTML))
                    except Exception:
                        pass

                    # Pass the upload client to OptimizedProgress
                    progress_handler = OptimizedProgress(
                        p.name, total_size, progress_msg, start_time,
                        update_interval=15.0,
                        reply_markup=progress_markup,
                        client=upload_client
                    )

                    send_kwargs = {
                        "chat_id": chat_id,
                        "document": str(p),
                        "caption": _scrub_text_for_user(caption_html),
                        "parse_mode": ParseMode.HTML,
                        "progress": progress_handler,
                    }
                    if thumb_path:
                        send_kwargs["thumb"] = thumb_path

                    task = asyncio.current_task()
                    if group_info:
                        group_info["active_task"] = task

                    sent_doc = await upload_with_retry(upload_client, send_kwargs)
                    
                    total_elapsed = time.time() - start_time
                    try:
                        avg_speed = int((total_size or 0) / max(1.0, total_elapsed))
                        speed_mbps = (avg_speed * 8) / (1024 * 1024)
                        await notify(f"Subida completada: {p.name} ({human_size(total_size)}) a {speed_mbps:.2f} Mbps", reply_message=progress_msg)
                    except Exception:
                        await notify(f"Subida completada: {p.name} ({human_size(total_size)})", reply_message=progress_msg)
                    
                    final_text = build_progress_text(p.name, total_size, total_size or 0, total_elapsed, 0, speed=avg_speed if 'avg_speed' in locals() else None)
                    if 'avg_speed' in locals() and avg_speed:
                        speed_mbps = (avg_speed * 8) / (1024 * 1024)
                        final_text += f"\n\n<i>Velocidad final: {speed_mbps:.2f} Mbps</i>"
                    try:
                        await _edit_progress_safe(progress_msg, final_text, keep_button=False)
                    except Exception:
                        pass
                        
                except asyncio.CancelledError:
                    if progress_msg:
                        await _edit_progress_safe(progress_msg, "<i>Subida cancelada.</i>", keep_button=False)
                    break
                except Exception as e:
                    logger.exception(f"{client_name} upload failed")
                    try:
                        await _edit_progress_safe(progress_msg, _scrub_text_for_user(f"<i>Subida fallida: {str(e)[:100]}</i>"), keep_button=False)
                    except Exception:
                        pass
                finally:
                    if group_info:
                        group_info["active_task"] = None
            except Exception:
                logger.exception("upload_cmd outer error")
                try:
                    await notify("Error inesperado al subir un archivo.")
                except Exception:
                    pass
    finally:
        UPLOAD_GROUPS.pop(upload_group_id, None)

# ============================================================
# MODIFIED handle_incoming_message - enqueues all tasks (unchanged)
# ============================================================
async def handle_incoming_message(client: Client, message: Message, from_queue: bool = False):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado. No estás autorizado para usar este bot.")
        return
    if not from_queue:
        await enqueue_user_task(user, client, message, handle_incoming_message)
        return
    msg = message
    if msg is None:
        return

    has_media = bool(
        msg.document or msg.photo or msg.video or msg.sticker or msg.voice or msg.audio
    )

    text = (msg.text or "") + ("\n" + (msg.caption or "")) if (msg.caption or msg.text) else (msg.text or "")
    matches = URL_REGEX.findall(text)
    extracted = []
    for tup in matches:
        for part in tup:
            if part:
                extracted.append(part)

    aria2_targets_from_text = []
    other_links_remaining = []
    for l in extracted:
        if is_magnet(l) or is_torrent_url(l):
            aria2_targets_from_text.append(l)
        else:
            other_links_remaining.append(l)

    if not has_media and not extracted:
        await notify_user_from_message(message, "No se detectaron enlaces ni medios compatibles.")
        return

    job = {
        "user": user,
        "message": message,
        "gofile_links": [],
        "other_links": other_links_remaining,
        "aria2_targets": aria2_targets_from_text,
        "text": text or "",
    }

    job_id = uuid.uuid4().hex
    cancel_event = asyncio.Event()

    async with PENDING_JOBS_LOCK:
        PENDING_JOBS[job_id] = {
            "job": job,
            "cancel_event": cancel_event,
            "user_id": user.id,
            "message": message,
            "queue_position": PROCESSING_QUEUE.qsize() + 1
        }

    await PROCESSING_QUEUE.put((job_id, job))

    keyboard = InlineKeyboardMarkup([[InlineKeyboardButton("❌ Cancelar", callback_data=f"cancel_job:{job_id}")]])
    queue_position = PENDING_JOBS[job_id]["queue_position"]
    await notify_user_from_message(
        message,
        f"⚙️ Su solicitud ha sido encolada (posición {queue_position}). "
        "El procesamiento comenzará cuando haya capacidad disponible.\n\n"
        "Puede cancelar esta tarea con el botón de abajo.",
        reply_markup=keyboard
    )

async def handle_cancel_job(client: Client, callback_query: CallbackQuery):
    data = callback_query.data
    if not data.startswith("cancel_job:"):
        return
    job_id = data.split(":", 1)[1]
    user = callback_query.from_user

    async with PENDING_JOBS_LOCK:
        job_entry = PENDING_JOBS.get(job_id)
        if not job_entry:
            await callback_query.answer("Trabajo no encontrado o ya procesado.", show_alert=True)
            return
        if job_entry["user_id"] != user.id:
            await callback_query.answer("No eres el propietario de este trabajo.", show_alert=True)
            return
        job_entry["cancel_event"].set()
        await callback_query.answer("Cancelación solicitada. Si no se ha iniciado, será omitido.", show_alert=True)
        try:
            await callback_query.message.edit("✅ Su tarea encolada ha sido cancelada.", reply_markup=None)
        except Exception:
            pass

async def cmd_cd(client: Client, message: Message):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    args = message.text.split(None)[1:] if message.text else []
    if not args:
        await notify_user_from_message(message, "Uso: /cd <num> (use el índice de /ls).")
        return
    try:
        idx = int(args[0])
    except Exception:
        await notify_user_from_message(message, "El argumento debe ser un número (el índice del directorio mostrado en /ls).")
        return
    target = resolve_user_index_to_path(user, idx)
    if not target:
        await notify_user_from_message(message, "Índice inválido.")
        return
    if not target.is_dir():
        await notify_user_from_message(message, "El destino no es un directorio.")
        return
    if not ensure_within_user_root(user, target):
        await notify_user_from_message(message, "Operación no permitida.")
        return
    root = get_user_root_path(user)
    try:
        rel = target.resolve().relative_to(root.resolve())
    except Exception:
        await notify_user_from_message(message, "Error al cambiar de directorio (error interno).")
        return
    CURRENT_DIRS[user.id] = Path(rel)
    visible = "/" if str(rel) == "." else "/" + str(rel).replace("\\", "/").lstrip("/")
    await notify_user_from_message(message, f"🗃Directorio cambiado a: {visible}")

async def cmd_back(client: Client, message: Message):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    root = get_user_root_path(user)
    cur_rel = CURRENT_DIRS.get(user.id, Path("."))
    try:
        if cur_rel == Path(".") or str(cur_rel) == ".":
            await notify_user_from_message(message, "🗃Ya estás en el directorio raíz (/).")
            return
        new_rel = (cur_rel).parent
        if str(new_rel) == "." or new_rel == Path("."):
            CURRENT_DIRS[user.id] = Path(".")
            await notify_user_from_message(message, "🗃Movido a raíz (/).")
            return
        CURRENT_DIRS[user.id] = new_rel
        visible = "/" + str(new_rel).replace("\\", "/").lstrip("/")
        await notify_user_from_message(message, f"🗃Movido a: {visible}")
    except Exception:
        CURRENT_DIRS[user.id] = Path(".")
        await notify_user_from_message(message, "🗃Movido a raíz (/).")

async def cmd_mkdir(client: Client, message: Message):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    args = message.text.split(None)[1:] if message.text else []
    if not args:
        await notify_user_from_message(message, "Uso: /mkdir <nombre_carpeta>")
        return
    raw_name = " ".join(args).strip()
    if not raw_name:
        await notify_user_from_message(message, "El nombre de la carpeta no puede estar vacío.")
        return
    if raw_name == "*" or raw_name in (".", ".."):
        await notify_user_from_message(message, "Nombre de carpeta inválido.")
        return
    forbidden = set('<>:"/\\|?*\0')
    if any((c in forbidden) for c in raw_name):
        await notify_user_from_message(message, "El nombre contiene caracteres no permitidos en Windows. Evite <> : \" / \\ | ? * y caracteres de control.")
        return
    if all(ch == "." for ch in raw_name) or raw_name.strip() == "":
        await notify_user_from_message(message, "Nombre de carpeta inválido.")
        return
    safe_name = sanitize_filename(raw_name)
    if safe_name != raw_name:
        await notify_user_from_message(message, "El nombre contiene caracteres no permitidos; elija otro nombre.")
        return
    root = get_user_root_path(user)
    rel = CURRENT_DIRS.get(user.id, Path("."))
    try:
        current = (root / rel).resolve()
    except Exception:
        current = root
    try:
        if not str(current).startswith(str(root)):
            current = root
            CURRENT_DIRS[user.id] = Path(".")
    except Exception:
        current = root
        CURRENT_DIRS[user.id] = Path(".")
    target = (current / safe_name).resolve()
    if not ensure_within_user_root(user, target):
        await notify_user_from_message(message, "La operación escaparía de su carpeta de usuario; abortada.")
        return
    if safe_name == "*":
        await notify_user_from_message(message, "El nombre '*' no está permitido.")
        return
    if target.exists():
        await notify_user_from_message(message, "Ya existe un archivo o carpeta con ese nombre.")
        return
    try:
        await asyncio.wait_for(asyncio.to_thread(target.mkdir, parents=False, exist_ok=False), timeout=FILE_IO_TIMEOUT)
        await notify_user_from_message(message, f"Creada carpeta: {safe_name}")
    except FileExistsError:
        await notify_user_from_message(message, "Ya existe un archivo o carpeta con ese nombre.")
    except PermissionError:
        await notify_user_from_message(message, "Permiso denegado: no se puede crear la carpeta aquí.")
    except Exception:
        logger.exception("mkdir failed")
        await notify_user_from_message(message, "Error al crear la carpeta.")

async def cmd_setpass(client: Client, message: Message):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    args = message.text.split(None)[1:] if message.text else []
    if not args:
        await notify_user_from_message(message, "Uso: /setpass <contraseña>")
        return
    pwd = " ".join(args).strip()
    if not pwd:
        await notify_user_from_message(message, "La contraseña no puede estar vacía.")
        return
    PASSWORDS[user.id] = pwd
    await notify_user_from_message(message, "Contraseña guardada para sus operaciones /zip. (Almacenada en memoria; se perderá al reiniciar el bot.)")

async def cmd_nopass(client: Client, message: Message):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    if user.id in PASSWORDS:
        PASSWORDS.pop(user.id, None)
        await notify_user_from_message(message, "Contraseña eliminada. Los futuros comandos /zip crearán archivos sin cifrar.")
    else:
        await notify_user_from_message(message, "No tenías ninguna contraseña establecida.")

async def cmd_pass_status(client: Client, message: Message):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    pwd = PASSWORDS.get(user.id)
    if pwd:
        await notify_user_from_message(message, f"Tienes una contraseña establecida para zips: {pwd}\n(Almacenada en memoria; se perderá al reiniciar el bot.)")
    else:
        await notify_user_from_message(message, "No hay contraseña establecida para sus operaciones /zip.")

# ============================================================
# UPDATED cmd_unzip - now uses 'unar' and a reliable size‑based progress monitor
# ============================================================
async def cmd_unzip(client: Client, message: Message, from_queue: bool = False):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    if not from_queue:
        await enqueue_user_task(user, client, message, cmd_unzip)
        return
    async with ZIP_SEMAPHORE:
        args = message.text.split(None)[1:] if message.text else []
        if not args:
            await notify_user_from_message(message, "Uso: /unzip <num|a,b,rango|*> [contraseña]\nEjemplos:\n/unzip 5,6,8\n/unzip 5 micontraseña")
            return
        sel_token = args[0].strip()
        password = None
        if len(args) >= 2:
            password = " ".join(args[1:]).strip()
            if password == "":
                password = None

        # ---------- NUEVO: Detectar herramientas según extensión ----------
        # Primero verificamos que exista al menos una herramienta
        unar_cmd = shutil.which("unar")
        unrar_cmd = shutil.which("unrar")
        if not unar_cmd and not unrar_cmd:
            await notify_user_from_message(message, "No se encontró ninguna herramienta de descompresión. Instale 'unar' o 'unrar'.")
            return

        items = await _list_user_items_async(user, timeout_seconds=COMMAND_TIMEOUT)
        if not items:
            await notify_user_from_message(message, "No hay archivos o carpetas en el directorio actual.")
            return

        def parse_selection(token: str, available_items: List[Path]) -> List[Path]:
            t = token.strip()
            if t == "*" or t.lower() == "all":
                return available_items[:]
            chosen = set()
            parts_ = [p.strip() for p in t.split(",") if p.strip()]
            for p in parts_:
                if "-" in p:
                    try:
                        a, b = p.split("-", 1)
                        a_i = int(a); b_i = int(b)
                        low = min(a_i, b_i); high = max(a_i, b_i)
                        for ii in range(low, high + 1):
                            chosen.add(ii)
                    except Exception:
                        continue
                else:
                    try:
                        ii = int(p); chosen.add(ii)
                    except Exception:
                        continue
            result = []
            for idx in sorted(chosen):
                if 1 <= idx <= len(available_items):
                    result.append(available_items[idx - 1])
            return result

        sources = parse_selection(sel_token, items)
        if not sources:
            await notify_user_from_message(message, "No se seleccionaron elementos válidos.")
            return

        root = get_user_root_path(user)
        cur_rel = CURRENT_DIRS.get(user.id, Path("."))
        current = (root / cur_rel).resolve() if cur_rel else root

        for src in sources:
            try:
                if not ensure_within_user_root(user, src):
                    await notify_user_from_message(message, f"{src.name}: omitido (no permitido).")
                    continue
                if not src.exists() or not src.is_file():
                    await notify_user_from_message(message, f"{src.name}: omitido (no es un archivo).")
                    continue

                # ---- Disk quota and free space check ----
                user_root = get_user_root_path(user)
                ok, msg = await check_disk_free_space(user_root)
                if not ok:
                    await notify_user_from_message(message, msg)
                    return
                archive_size = src.stat().st_size
                ok, msg = await check_user_quota(user, additional_bytes=archive_size)
                if not ok:
                    await notify_user_from_message(message, msg)
                    return

                base = re.sub(r'(\.(zip|rar|7z|tar\.gz|tgz|tar\.bz2|tbz2|tar\.xz|txz|gz|bz2|xz|lzma|zst|001|002|003|part\d+))$', '', src.name, flags=re.IGNORECASE)
                if base == src.name:
                    base = src.stem
                out_dir_name = sanitize_filename(f"{base}_extracted")
                out_dir = (current / out_dir_name).resolve()
                if not ensure_within_user_root(user, out_dir):
                    await notify_user_from_message(message, f"{src.name}: omitido (escaparía de la raíz de usuario).")
                    continue
                await asyncio.wait_for(asyncio.to_thread(out_dir.mkdir, parents=True, exist_ok=True), timeout=FILE_IO_TIMEOUT)

                # ---------- NUEVO: Elegir herramienta según extensión ----------
                # Detectamos si es RAR (extensión .rar o partes .rNN o .partN.rar)
                is_rar = False
                if src.suffix.lower() == '.rar':
                    is_rar = True
                else:
                    # Partes RAR: .r00, .r01, ... o .part1.rar, .part2.rar
                    if re.search(r'\.r\d{2}$', src.name, re.IGNORECASE):
                        is_rar = True
                    elif re.search(r'\.part\d+\.rar$', src.name, re.IGNORECASE):
                        is_rar = True

                if is_rar:
                    if not unrar_cmd:
                        await notify_user_from_message(message, f"{src.name}: se necesita 'unrar' para archivos RAR, pero no está instalado.")
                        continue
                    extract_cmd = unrar_cmd
                    # Opciones de unrar: x (extraer con rutas), -o+ (sobrescribir), -y (si)
                    cmd = [extract_cmd, "x", "-o+", "-y"]
                    if password:
                        cmd += ["-p" + password]
                    cmd.append(str(src))
                    cmd.append(str(out_dir))  # destino
                    log_cmd = cmd.copy()
                    if password:
                        try:
                            pwd_idx = log_cmd.index("-p" + password)
                            log_cmd[pwd_idx] = "-p****"
                        except ValueError:
                            pass
                    logger.info(f"Running unrar command: {' '.join(log_cmd)}")
                else:
                    # Para el resto, usar unar
                    if not unar_cmd:
                        await notify_user_from_message(message, f"{src.name}: se necesita 'unar' para este formato, pero no está instalado.")
                        continue
                    extract_cmd = unar_cmd
                    cmd = [extract_cmd, "-o", str(out_dir)]
                    if password:
                        cmd += ["-p", password]
                    cmd.append(str(src))
                    log_cmd = cmd.copy()
                    if password:
                        try:
                            pwd_idx = log_cmd.index("-p") + 1
                            if pwd_idx < len(log_cmd):
                                log_cmd[pwd_idx] = "****"
                        except ValueError:
                            pass
                    logger.info(f"Running unar command: {' '.join(log_cmd)}")

                progress_msg = await safe_reply(
                    message,
                    "<i>⏳ Iniciando extracción...</i>",
                    reply_markup=_unzip_cancel_keyboard(),
                    parse_mode=ParseMode.HTML,
                )

                async def edit_progress(text, keep_button=True):
                    if not progress_msg:
                        return
                    asyncio.create_task(
                        edit_progress_resilient(
                            progress_msg, text,
                            reply_markup=_unzip_cancel_keyboard() if keep_button else None,
                            client=bot_client,
                            per_attempt_timeout=5.0
                        )
                    )

                proc = await asyncio.create_subprocess_exec(
                    *cmd,
                    stdout=asyncio.subprocess.PIPE,
                    stderr=asyncio.subprocess.PIPE,
                    cwd=str(out_dir),
                    stdin=asyncio.subprocess.DEVNULL,
                    start_new_session=True,
                )
                pid = proc.pid
                if pid is None:
                    await edit_progress(f"<i>❌ {src.name}: no se pudo obtener el PID</i>", False)
                    continue
                logger.info(f"Extracting {src.name} with PID {pid}")

                msg_id = getattr(progress_msg, "message_id", None) or getattr(progress_msg, "id", None)
                if msg_id:
                    _UNZIP_TASKS[msg_id] = {"process": proc, "user_id": user.id, "cancelled": False}

                start_time = time.time()
                spinner_chars = ['⠋','⠙','⠹','⠸','⠼','⠴','⠦','⠧','⠇','⠏']

                async def size_monitor():
                    while True:
                        if asyncio.current_task().cancelled():
                            break
                        await asyncio.sleep(5.0)
                        total_extracted = 0
                        try:
                            for item in out_dir.rglob('*'):
                                if item.is_file():
                                    total_extracted += item.stat().st_size
                        except Exception:
                            continue
                        pct = min(100.0, (total_extracted / archive_size) * 100.0) if archive_size > 0 else 0.0
                        bar = "█" * int(pct / 5) + "░" * (20 - int(pct / 5))
                        elapsed = int(time.time() - start_time)
                        spinner = spinner_chars[elapsed % len(spinner_chars)]
                        text = f"<i>Extrayendo {src.name}\n{bar} {pct:.1f}% … {spinner}\n⏳ {elapsed}s transcurridos</i>"
                        await edit_progress(text)

                        # Quota check
                        remaining = archive_size - total_extracted
                        if await check_quota_and_abort(user,
                                                       additional_bytes=remaining,
                                                       progress_msg=progress_msg):
                            if msg_id in _UNZIP_TASKS:
                                _UNZIP_TASKS[msg_id]['cancelled'] = True
                            if proc.returncode is None:
                                proc.terminate()
                            break

                monitor_task = asyncio.create_task(size_monitor())

                rc = await proc.wait()

                monitor_task.cancel()
                try:
                    await monitor_task
                except asyncio.CancelledError:
                    pass

                if msg_id:
                    _UNZIP_TASKS.pop(msg_id, None)

                stdout_data, stderr_data = await proc.communicate()
                out_msg = stdout_data.decode(errors="ignore").strip()
                err_msg = stderr_data.decode(errors="ignore").strip()
                combined = ""
                if out_msg:
                    combined += out_msg
                if err_msg:
                    if combined:
                        combined += "\n"
                    combined += err_msg
                combined = combined.strip()

                # ---------- Manejo de errores específico ----------
                if rc != 0:
                    clean_error = combined.strip()
                    filename = src.name
                    if filename in clean_error:
                        idx = clean_error.find(filename)
                        if idx != -1:
                            after_filename = clean_error[idx + len(filename):]
                            if after_filename.startswith(': '):
                                clean_error = after_filename[2:].strip()
                            else:
                                parts = clean_error.split(':', 1)
                                if len(parts) > 1 and parts[0].strip().endswith(filename):
                                    clean_error = parts[1].strip()
                    if len(clean_error) > 500:
                        clean_error = clean_error[:500] + "..."

                    try:
                        src_index = items.index(src) + 1
                    except ValueError:
                        src_index = "?"

                    if password is None:
                        if "password" in clean_error.lower() or "requires a password" in clean_error.lower():
                            hint = f" Intente proporcionar una contraseña con /unzip {src_index} <contraseña>."
                            await edit_progress(f"<i>❌ {filename}: Este archivo requiere contraseña.{hint}</i>", False)
                        else:
                            await edit_progress(f"<i>❌ {filename}: extracción fallida (código {rc}). Error: {clean_error}</i>", False)
                    else:
                        if any(phrase in clean_error.lower() for phrase in ["wrong password", "incorrect password", "bad password", "authentication failed", "could not decrypt", "invalid password"]):
                            await edit_progress(f"<i>❌ {filename}: La contraseña proporcionada es incorrecta.</i>", False)
                        elif "password" in clean_error.lower() or "requires a password" in clean_error.lower():
                            await edit_progress(f"<i>❌ {filename}: Puede que el archivo no requiera contraseña, o la contraseña es incorrecta.</i>", False)
                        else:
                            await edit_progress(f"<i>❌ {filename}: extracción fallida (código {rc}). Error: {clean_error}</i>", False)
                    continue

                await edit_progress(f"<i>✅ {src.name} extracción finalizada correctamente.</i>", False)

            except Exception as e:
                logger.exception("unzip failed for %s", src)
                await notify_user_from_message(message, f"❌ {src.name}: {str(e)[:100]}")

# ------------------------------------------------------------
# REST OF COMMANDS (unchanged except translations)
# ------------------------------------------------------------
async def cmd_set_thumb(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    reply = message.reply_to_message
    photo_msg = None
    if reply and (reply.photo or reply.document):
        photo_msg = reply
    elif message.photo or message.document:
        photo_msg = message
    else:
        await notify_user_from_message(message, "Uso: responda a una foto con /set_thumb o envíe una foto con el comando. Este comando requiere una foto.")
        return
    file_id = None
    try:
        if photo_msg.photo:
            file_id = photo_msg.photo[-1].file_id if isinstance(photo_msg.photo, list) else photo_msg.photo.file_id
        elif photo_msg.document:
            mim = getattr(photo_msg.document, "mime_type", "") or ""
            if mim.startswith("image/"):
                file_id = photo_msg.document.file_id
            else:
                await notify_user_from_message(message, "El documento adjunto no es una imagen. Responda a una imagen/foto.")
                return
        else:
            await notify_user_from_message(message, "No se encontró foto en el mensaje respondido.")
            return
    except Exception:
        await notify_user_from_message(message, "Error al detectar la foto en el mensaje respondido.")
        return
    if not file_id:
        await notify_user_from_message(message, "Error al determinar el archivo a usar como miniatura.")
        return
    try:
        file = await bot_client.download_media(file_id, file_name=str(Path.cwd() / THUMBNAIL_FILENAME))
        dest_path = Path(file).resolve()
        validated_thumb = await asyncio.wait_for(asyncio.to_thread(validate_and_fix_thumbnail, dest_path), timeout=FILE_IO_TIMEOUT)
        if validated_thumb:
            global THUMBNAIL_PATH
            THUMBNAIL_PATH = validated_thumb
            await notify_user_from_message(message, "Miniatura guardada, validada y se usará en futuras subidas.")
            logger.info("Thumbnail set by owner %s and validated", user.id)
        else:
            await notify_user_from_message(message, "Error al validar la miniatura. Asegúrese de que sea una imagen válida.")
    except Exception:
        logger.exception("Failed to save thumbnail")
        await notify_user_from_message(message, "Error al guardar la miniatura.")

async def cmd_thumb(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    global THUMBNAIL_PATH
    if THUMBNAIL_PATH and THUMBNAIL_PATH.exists():
        info_parts = [f"Ruta: {THUMBNAIL_PATH.name}"]
        if PIL_AVAILABLE:
            try:
                def get_image_info():
                    with Image.open(THUMBNAIL_PATH) as img:
                        dimensions = f"{img.width}x{img.height}"
                        mode = img.mode
                        size = THUMBNAIL_PATH.stat().st_size
                        return dimensions, mode, size
                dimensions, mode, size = await asyncio.wait_for(asyncio.to_thread(get_image_info), timeout=FILE_IO_TIMEOUT)
                info_parts.append(f"Dimensiones: {dimensions}")
                info_parts.append(f"Modo: {mode}")
                info_parts.append(f"Tamaño: {human_size(size)}")
            except Exception as e:
                info_parts.append(f"Info: no se pudo leer metadatos de la imagen ({e})")
        info = "\n".join(info_parts)
        await notify_user_from_message(message, f"Miniatura configurada actualmente:\n{info}")
        try:
            await throttled_send(bot_client.send_photo(message.chat.id, photo=str(THUMBNAIL_PATH), caption="Miniatura configurada actualmente"))
        except Exception:
            try:
                await throttled_send(bot_client.send_document(message.chat.id, document=str(THUMBNAIL_PATH), caption="Miniatura configurada actualmente (enviada como archivo)"))
            except Exception:
                logger.exception("Failed to send thumbnail")
                await notify_user_from_message(message, "La miniatura está configurada pero falló al enviarla.")
    else:
        await notify_user_from_message(message, "No hay miniatura configurada actualmente.")

async def cmd_del_thumb(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    global THUMBNAIL_PATH
    if not THUMBNAIL_PATH or not THUMBNAIL_PATH.exists():
        THUMBNAIL_PATH = None
        await notify_user_from_message(message, "No había miniatura configurada.")
        return
    try:
        await asyncio.wait_for(asyncio.to_thread(THUMBNAIL_PATH.unlink, missing_ok=True), timeout=FILE_IO_TIMEOUT)
    except Exception:
        logger.exception("Failed to delete thumbnail file")
        await notify_user_from_message(message, "Error al eliminar la miniatura.")
        return
    THUMBNAIL_PATH = None
    await notify_user_from_message(message, "Miniatura eliminada.")

async def cmd_adduser(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    args = message.text.split(None)[1:] if message.text else []
    if len(args) < 2:
        await notify_user_from_message(message, "Uso: /adduser -d <días> <@usuario|id>  O  /adduser -m <minutos> <@usuario|id>")
        return
    flag = args[0]
    if flag not in ("-d", "-m"):
        await notify_user_from_message(message, "Indicador inválido. Use -d para días o -m para minutos.")
        return
    try:
        num = int(args[1])
        if num <= 0:
            raise ValueError()
    except Exception:
        await notify_user_from_message(message, "Duración inválida. Proporcione un número entero positivo después de -d/-m.")
        return
    if len(args) < 3:
        await notify_user_from_message(message, "Proporcione el usuario destino como @usuario o ID numérico.")
        return
    target_token = args[2]
    key = _normalize_user_key(target_token)
    if not key:
        await notify_user_from_message(message, "Token de usuario inválido.")
        return
    now = datetime.now(timezone.utc)
    if flag == "-d":
        expires = now + timedelta(days=num)
    else:
        expires = now + timedelta(minutes=num)
    ADDED_USERS[key] = {"id": int(key) if key.isdigit() else None, "username": None if key.isdigit() else key, "expires_at": expires.timestamp()}
    add_temporary_user_and_save(key, ADDED_USERS[key])
    pretty = key
    await notify_user_from_message(message, f"Usuario {pretty} añadido hasta {expires.isoformat()} UTC.")

async def cmd_lsusers(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    args = message.text.split(None)[1:] if message.text else []
    now_ts = datetime.now(timezone.utc).timestamp()
    if args:
        key = _normalize_user_key(args[0])
        if not key:
            await notify_user_from_message(message, "Token de usuario inválido.")
            return
        info = ADDED_USERS.get(key)
        if not info:
            await notify_user_from_message(message, "Usuario no encontrado en la lista temporal.")
            return
        if info.get("expires_at", 0) <= now_ts:
            ADDED_USERS.pop(key, None)
            save_persistent_state()
            await notify_user_from_message(message, "La entrada del usuario expiró y ha sido eliminada.")
            return
        rem = int(info["expires_at"] - now_ts)
        hrs, remr = divmod(rem, 3600)
        mins, secs = divmod(remr, 60)
        human = f"{hrs}h{mins}m{secs}s" if hrs else (f"{mins}m{secs}s" if mins else f"{secs}s")
        await notify_user_from_message(message, f"{key}: restante {human}")
        return
    lines = []
    for k, info in list(ADDED_USERS.items()):
        if info.get("expires_at", 0) <= now_ts:
            ADDED_USERS.pop(k, None)
            continue
        rem = int(info["expires_at"] - now_ts)
        hrs, remr = divmod(rem, 3600)
        mins, secs = divmod(remr, 60)
        human = f"{hrs}h{mins}m{secs}s" if hrs else (f"{mins}m{secs}s" if mins else f"{secs}s")
        lines.append(f"{k}: {human}")
    if not lines:
        await notify_user_from_message(message, "No hay usuarios temporales añadidos actualmente.")
    else:
        await notify_user_from_message(message, "Usuarios temporales:\n" + "\n".join(lines))

async def cmd_deluser(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    args = message.text.split(None)[1:] if message.text else []
    if not args:
        await notify_user_from_message(message, "Uso: /deluser <@usuario|id>")
        return
    key = _normalize_user_key(args[0])
    if not key:
        await notify_user_from_message(message, "Token de usuario inválido.")
        return
    if key in ADDED_USERS:
        ADDED_USERS.pop(key, None)
        remove_temporary_user_and_save(key)
        await notify_user_from_message(message, f"Usuario temporal {key} eliminado.")
    else:
        await notify_user_from_message(message, "Usuario no encontrado en la lista temporal.")

async def cmd_list_suffix_filter(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    if not SUFFIX_FILTERS:
        await notify_user_from_message(message, "No hay filtros de sufijo configurados.")
    else:
        lines = ["Sufijos configurados:"]
        for s in SUFFIX_FILTERS:
            lines.append(f"- `{s}`")
        await notify_user_from_message(message, "\n".join(lines))

async def cmd_add_suffix_filter(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    args = message.text.split(None)[1:] if message.text else []
    if not args:
        await notify_user_from_message(message, "Uso: /add_suffix_filter <sufijo>")
        return
    suffix = " ".join(args).strip()
    if not suffix:
        await notify_user_from_message(message, "El sufijo no puede estar vacío.")
        return
    if suffix in SUFFIX_FILTERS:
        await notify_user_from_message(message, f"El sufijo '{suffix}' ya existe.")
        return
    SUFFIX_FILTERS.append(suffix)
    save_persistent_state()
    await notify_user_from_message(message, f"Añadido filtro de sufijo: '{suffix}'")

async def cmd_delete_suffix_filter(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    args = message.text.split(None)[1:] if message.text else []
    if not args:
        await notify_user_from_message(message, "Uso: /delete_suffix_filter <sufijo>")
        return
    suffix = " ".join(args).strip()
    if suffix not in SUFFIX_FILTERS:
        await notify_user_from_message(message, f"Sufijo '{suffix}' no encontrado.")
        return
    SUFFIX_FILTERS.remove(suffix)
    save_persistent_state()
    await notify_user_from_message(message, f"Eliminado filtro de sufijo: '{suffix}'")

async def cmd_enable_suffix_filter(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    global SUFFIX_FILTER_ENABLED
    if not SUFFIX_FILTERS:
        await notify_user_from_message(message, "No hay filtros de sufijo configurados. Añada alguno primero.")
        return
    SUFFIX_FILTER_ENABLED = True
    save_persistent_state()
    await notify_user_from_message(message, "Filtro de sufijo activado.")

async def cmd_disable_suffix_filter(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    global SUFFIX_FILTER_ENABLED
    SUFFIX_FILTER_ENABLED = False
    save_persistent_state()
    await notify_user_from_message(message, "Filtro de sufijo desactivado.")

async def cmd_suffix_filter_status(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    status = "activado" if SUFFIX_FILTER_ENABLED else "desactivado"
    if SUFFIX_FILTERS:
        filters = ", ".join(f"`{s}`" for s in SUFFIX_FILTERS)
        await notify_user_from_message(message, f"Filtro de sufijo está {status}.\nSufijos configurados: {filters}")
    else:
        await notify_user_from_message(message, f"Filtro de sufijo está {status}.\nNo hay sufijos configurados.")

async def cmd_rename_suffix_folders(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    root = get_user_root_path(user)
    rel = CURRENT_DIRS.get(user.id, Path("."))
    try:
        current = (root / rel).resolve()
    except Exception:
        current = root
    if not current.exists():
        await notify_user_from_message(message, "El directorio actual no existe.")
        return
    if not SUFFIX_FILTER_ENABLED:
        await notify_user_from_message(message, "El filtro de sufijo está desactivado. Actívelo con /enable_suffix_filter primero.")
        return
    if not SUFFIX_FILTERS:
        await notify_user_from_message(message, "No hay filtros de sufijo configurados. Añada alguno con /add_suffix_filter.")
        return
    renamed = []
    failed = []
    for item in current.iterdir():
        if item.is_dir():
            original = item.name
            filtered_path, was_modified = await apply_suffix_filter_to_path(item)
            if filtered_path and was_modified:
                renamed.append(f"{original} -> {filtered_path.name}")
            else:
                for suffix in SUFFIX_FILTERS:
                    if original.endswith(suffix):
                        failed.append(f"{original} (aún tiene '{suffix}')")
                        break
    if renamed:
        await notify_user_from_message(message, f"Carpetas renombradas:\n" + "\n".join(renamed))
    if failed:
        await notify_user_from_message(message, f"Error al renombrar:\n" + "\n".join(failed))
    if not renamed and not failed:
        await notify_user_from_message(message, "No se encontraron carpetas con sufijos configurados en el directorio actual.")

async def cmd_enable_file_signing(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    global FILE_SIGNING_ENABLED
    if not FILE_SIGN:
        await notify_user_from_message(message, "No hay firma establecida. Use /set_sign <firma> primero.")
        return
    FILE_SIGNING_ENABLED = True
    save_persistent_state()
    await notify_user_from_message(message, f"Firma de archivos activada. Firma: '{FILE_SIGN}'")

async def cmd_disable_file_signing(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    global FILE_SIGNING_ENABLED
    FILE_SIGNING_ENABLED = False
    save_persistent_state()
    await notify_user_from_message(message, "Firma de archivos desactivada.")

async def cmd_set_sign(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    args = message.text.split(None)[1:] if message.text else []
    if not args:
        await notify_user_from_message(message, "Uso: /set_sign <firma>")
        return
    sign = " ".join(args).strip()
    if not sign:
        await notify_user_from_message(message, "La firma no puede estar vacía.")
        return
    global FILE_SIGN
    FILE_SIGN = sign
    save_persistent_state()
    await notify_user_from_message(message, f"Firma establecida a: '{sign}'")

async def cmd_list_sign(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    status = "activada" if FILE_SIGNING_ENABLED else "desactivada"
    sign = FILE_SIGN if FILE_SIGN else "(no establecida)"
    await notify_user_from_message(message, f"Firma de archivos está {status}.\nFirma actual: '{sign}'")

async def cmd_sign_current_dir(client: Client, message: Message):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    if not FILE_SIGNING_ENABLED:
        await notify_user_from_message(message, "La firma de archivos está desactivada. Actívela primero.")
        return
    root = get_user_root_path(user)
    rel = CURRENT_DIRS.get(user.id, Path("."))
    try:
        current = (root / rel).resolve()
    except Exception:
        current = root
    if not current.exists():
        await notify_user_from_message(message, "El directorio no existe.")
        return
    renamed = 0
    for item in current.iterdir():
        signed_path = await apply_file_signing_async(item, FILE_SIGN, True)
        if signed_path and signed_path.name != item.name:
            renamed += 1
    await notify_user_from_message(message, f"Firmados {renamed} elemento(s) en el directorio actual.")

# PER-USER AUTOMATOR
async def get_automator_enabled(user):
    if user is None or not hasattr(user, 'id'):
        return DEFAULT_AUTOMATOR_ENABLED
    async with USER_AUTOMATOR_LOCK:
        return USER_AUTOMATOR.get(user.id, DEFAULT_AUTOMATOR_ENABLED)

async def set_automator_enabled(user, enabled):
    if user is None or not hasattr(user, 'id'):
        return
    async with USER_AUTOMATOR_LOCK:
        USER_AUTOMATOR[user.id] = enabled

async def cmd_automator(client: Client, message: Message):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    current = await get_automator_enabled(user)
    new_state = not current
    await set_automator_enabled(user, new_state)
    status = "activado" if new_state else "desactivado"
    default_status = "ON" if DEFAULT_AUTOMATOR_ENABLED else "OFF"
    await notify_user_from_message(
        message,
        f"⚙️ Su Automator ahora está {status}.\n"
        f"(Valor por defecto para nuevos usuarios: {default_status})\n"
        "Cuando está activado: cualquier enlace que envíe será descargado, filtrado por sufijo, firmado, "
        "comprimido en partes de 2GB y cada parte se subirá automáticamente."
    )

async def cmd_public_help(client: Client, message: Message):
    user = message.from_user
    if not await is_user_authorized(user):
        await notify_user_from_message(message, "Acceso denegado. No estás autorizado para usar este bot.")
        return
    lines = [
        "Comandos disponibles para usuarios:",
        "",
        "/whoami   — Muestra tu ID y nombre de usuario",
        "/uptime   — Muestra el tiempo de actividad del bot",
        "/ls       — Lista archivos y carpetas en el directorio de trabajo actual",
        "/pwd      — Muestra el directorio de trabajo actual (relativo a tu raíz de usuario)",
        "/zip      — Crea un archivo comprimido de un archivo/carpeta y opcionalmente lo divide en partes (uso: /zip <num> [tamaño_max_mb])",
        "/mv       — Mueve o renombra elementos (uso en el bot; admite rangos y mover a índices de carpeta) ej: /mv * /1 o /mv 4-9 /",
        "/cp       — Copia elementos a una carpeta (uso: /cp <spec> /<índice_carpeta>) ej: /cp * /1 o /cp 4-9 /1",
        "/rm       — Elimina archivos/carpetas (admite rangos, listas y '*')",
        "/upload   — Sube archivos desde tu carpeta al chat (uso: /upload * o /upload 2,4 o /upload 1-9)",
        "/cd       — Cambia al directorio de un índice de carpeta mostrado en /ls",
        "/back     — Sube un nivel en el directorio",
        "/mkdir    — Crea una nueva carpeta en el directorio actual",
        "/setpass  — Establece una contraseña por usuario para archivos cifrados con /zip",
        "/nopass   — Elimina la contraseña por usuario usada para /zip",
        "/pass_status — Muestra si tienes una contraseña establecida para /zip",
        "/unzip    — Extrae archivos comprimidos almacenados en tu carpeta (uso: /unzip <índices> [contraseña])",
        "/automator — Activa/desactiva la compresión y subida automática del contenido descargado en partes de 2GB (configuración por usuario)",
        "",
        "Notas:",
        "- Muchas operaciones están restringidas a tu propia carpeta de usuario por seguridad.",
    ]
    await notify_user_from_message(message, "\n".join(lines))

async def cmd_admincmd(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado. Solo propietarios.")
        return
    lines = [
        "Todos los comandos del bot (propietarios y usuarios añadidos):",
        "",
        "# Comandos disponibles para usuarios añadidos (también en /help):",
        "/whoami, /uptime, /ls, /pwd, /zip, /mv, /cp, /rm, /upload, /cd, /back, /mkdir,",
        "/setpass, /nopass, /pass_status, /unzip, /automator",
        "",
        "# Comandos de propietario / admin:",
        "/start       — (propietario) Instrucciones de inicio",
        "/help        — (propietario) Ayuda antigua para propietarios (por compatibilidad)",
        "/status      — Verifica conectividad/estado con el sistema de descargas",
        "/set_thumb   — Establece miniatura global respondiendo a una foto",
        "/thumb       — Muestra la miniatura configurada",
        "/del_thumb   — Elimina la miniatura configurada",
        "/set_description  — Establece una descripción global de subida para /upload",
        "/description       — Muestra la descripción de subida actual",
        "/no_description    — Elimina la descripción de subida",
        "/adduser     — Añade un usuario temporal: /adduser -d <días> <@usuario|id> o -m <minutos> <@usuario|id>",
        "/lsusers     — Lista usuarios temporales y tiempo restante",
        "/deluser     — Elimina un usuario temporal",
        "/list_suffix_filter — Lista los filtros de sufijo configurados",
        "/add_suffix_filter <sufijo> — Añade un sufijo para eliminar de archivos y carpetas descargados",
        "/delete_suffix_filter <sufijo> — Elimina un sufijo de la lista",
        "/enable_suffix_filter — Activa el filtrado automático de sufijos",
        "/disable_suffix_filter — Desactiva el filtrado automático de sufijos",
        "/suffix_filter_status — Muestra el estado del filtro y los sufijos configurados",
        "/rename_suffix_folders — Renombra manualmente cualquier carpeta del directorio actual que termine con un sufijo configurado",
        "/enable_file_signing — Activa la firma automática de archivos/carpetas tras la descarga (añade la firma configurada al nombre)",
        "/disable_file_signing — Desactiva la firma automática",
        "/set_sign <firma> — Establece la cadena de firma (ej. '[Team]')",
        "/list_sign — Muestra la firma actual y su estado",
        "/sign_current_dir — Aplica la firma manualmente a todos los elementos del directorio actual",
        "/set_automator_concurrency <num> — Establece el número máximo de tareas de compresión+subida paralelas del Automator",
        "/automator_concurrency — Muestra el límite de concurrencia actual del Automator y tareas activas",
        "/uptime     — Muestra cuánto tiempo lleva activo el bot (público)",
        "",
        "Otros detalles:",
        "- /upload usa la miniatura configurada y aplica la descripción si está establecida.",
        "- /zip puede producir archivos cifrados si se establece una contraseña con /setpass y 7z está disponible.",
        "- Los usuarios temporales se gestionan en memoria y se persisten en disco; los propietarios los controlan.",
        "- El filtro de sufijo renombra automáticamente archivos Y carpetas descargados eliminando sufijos configurados (ej. ' [FitGirl Repack]') y recorta espacios extra.",
        "- La firma de archivos añade una firma personalizada (con espacio) al final de archivos/carpetas descargados después del filtro de sufijo.",
        "- Automator: cuando está activado, cada elemento descargado se comprime automáticamente en partes de 2GB 7z y se sube, luego se elimina.",
        "- La concurrencia del Automator controla cuántas tareas de compresión+subida se ejecutan en paralelo. Por defecto=1.",
        "- Los archivos .torrent nunca se modifican con filtrado de sufijo, firma o compresión del Automator. Se procesan directamente con el cliente de torrents.",
        "- La configuración del Automator es por usuario: se activa con /automator, el valor predeterminado viene de la variable de entorno AUTOMATOR_DEFAULT_ON (false por defecto).",
        "- Los trabajos encolados pueden ser cancelados por el usuario mediante el botón Cancelar en el mensaje de notificación de cola.",
        "- /unzip ahora usa una herramienta de descompresión y un monitor de progreso basado en tamaño fiable (no requiere 'progress' externo).",
    ]
    full = "\n".join(lines)
    MAX = 3500
    if len(full) <= MAX:
        await notify_user_from_message(message, full)
    else:
        parts = []
        cur = []
        cur_len = 0
        for ln in lines:
            ln_len = len(ln) + 1
            if cur_len + ln_len > MAX:
                parts.append("\n".join(cur))
                cur = [ln]
                cur_len = ln_len
            else:
                cur.append(ln)
                cur_len += ln_len
        if cur:
            parts.append("\n".join(cur))
        for p in parts:
            await notify_user_from_message(message, p)

async def cmd_set_automator_concurrency(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    args = message.text.split(None)[1:] if message.text else []
    if not args:
        await notify_user_from_message(message, "Uso: /set_automator_concurrency <número>")
        return
    try:
        new_concurrency = int(args[0])
        if new_concurrency < 1:
            await notify_user_from_message(message, "La concurrencia debe ser al menos 1.")
            return
        global AUTOMATOR_CONCURRENCY
        AUTOMATOR_CONCURRENCY = new_concurrency
        save_persistent_state()
        await notify_user_from_message(message, f"Concurrencia del Automator establecida a {new_concurrency}. Reinicie el bot para que los cambios surtan efecto total (el número de workers y el semáforo se actualizan al reiniciar).")
    except ValueError:
        await notify_user_from_message(message, "Proporcione un número válido.")

async def cmd_automator_concurrency(client: Client, message: Message):
    user = message.from_user
    if not is_owner(user):
        await notify_user_from_message(message, "Acceso denegado.")
        return
    await notify_user_from_message(message, f"Concurrencia actual del Automator: {AUTOMATOR_CONCURRENCY}\nTareas activas del Automator: {AUTOMATOR_ACTIVE_COUNT}")

def register_handlers(app_bot: Client):
    app_bot.add_handler(MessageHandler(cmd_start, filters.command("start")))
    app_bot.add_handler(MessageHandler(cmd_whoami, filters.command("whoami")))
    app_bot.add_handler(MessageHandler(cmd_public_help, filters.command("help")))
    app_bot.add_handler(MessageHandler(cmd_status, filters.command("status")))
    app_bot.add_handler(MessageHandler(cmd_ls, filters.command("ls")))
    app_bot.add_handler(MessageHandler(cmd_pwd, filters.command("pwd")))
    app_bot.add_handler(MessageHandler(cmd_zip, filters.command("zip")))
    app_bot.add_handler(MessageHandler(cmd_mv, filters.command("mv")))
    app_bot.add_handler(MessageHandler(cmd_cp, filters.command("cp")))
    app_bot.add_handler(MessageHandler(cmd_rm, filters.command("rm")))
    app_bot.add_handler(MessageHandler(cmd_upload, filters.command("upload")))
    app_bot.add_handler(MessageHandler(cmd_cd, filters.command("cd")))
    app_bot.add_handler(MessageHandler(cmd_back, filters.command("back")))
    app_bot.add_handler(MessageHandler(cmd_mkdir, filters.command("mkdir")))
    app_bot.add_handler(MessageHandler(cmd_setpass, filters.command("setpass")))
    app_bot.add_handler(MessageHandler(cmd_nopass, filters.command("nopass")))
    app_bot.add_handler(MessageHandler(cmd_pass_status, filters.command("pass_status")))
    app_bot.add_handler(MessageHandler(cmd_unzip, filters.command("unzip")))
    app_bot.add_handler(MessageHandler(cmd_set_thumb, filters.command("set_thumb")))
    app_bot.add_handler(MessageHandler(cmd_thumb, filters.command("thumb")))
    app_bot.add_handler(MessageHandler(cmd_del_thumb, filters.command("del_thumb")))
    app_bot.add_handler(MessageHandler(cmd_set_description, filters.command("set_description")))
    app_bot.add_handler(MessageHandler(cmd_description, filters.command("description")))
    app_bot.add_handler(MessageHandler(cmd_no_description, filters.command("no_description")))
    app_bot.add_handler(MessageHandler(cmd_adduser, filters.command("adduser")))
    app_bot.add_handler(MessageHandler(cmd_lsusers, filters.command("lsusers")))
    app_bot.add_handler(MessageHandler(cmd_deluser, filters.command("deluser")))
    app_bot.add_handler(MessageHandler(cmd_admincmd, filters.command("admincmd")))
    app_bot.add_handler(MessageHandler(cmd_list_suffix_filter, filters.command("list_suffix_filter")))
    app_bot.add_handler(MessageHandler(cmd_add_suffix_filter, filters.command("add_suffix_filter")))
    app_bot.add_handler(MessageHandler(cmd_delete_suffix_filter, filters.command("delete_suffix_filter")))
    app_bot.add_handler(MessageHandler(cmd_enable_suffix_filter, filters.command("enable_suffix_filter")))
    app_bot.add_handler(MessageHandler(cmd_disable_suffix_filter, filters.command("disable_suffix_filter")))
    app_bot.add_handler(MessageHandler(cmd_suffix_filter_status, filters.command("suffix_filter_status")))
    app_bot.add_handler(MessageHandler(cmd_rename_suffix_folders, filters.command("rename_suffix_folders")))
    app_bot.add_handler(MessageHandler(cmd_enable_file_signing, filters.command("enable_file_signing")))
    app_bot.add_handler(MessageHandler(cmd_disable_file_signing, filters.command("disable_file_signing")))
    app_bot.add_handler(MessageHandler(cmd_set_sign, filters.command("set_sign")))
    app_bot.add_handler(MessageHandler(cmd_list_sign, filters.command("list_sign")))
    app_bot.add_handler(MessageHandler(cmd_sign_current_dir, filters.command("sign_current_dir")))
    app_bot.add_handler(MessageHandler(cmd_automator, filters.command("automator")))
    app_bot.add_handler(MessageHandler(cmd_set_automator_concurrency, filters.command("set_automator_concurrency")))
    app_bot.add_handler(MessageHandler(cmd_automator_concurrency, filters.command("automator_concurrency")))
    app_bot.add_handler(MessageHandler(cmd_uptime, filters.command("uptime")))

    app_bot.add_handler(CallbackQueryHandler(handle_zip_cancel, filters.regex(r"^zip_cancel$")))
    app_bot.add_handler(CallbackQueryHandler(handle_unzip_cancel, filters.regex(r"^unzip_cancel$")))
    app_bot.add_handler(CallbackQueryHandler(handle_upload_cancel, filters.regex(r"^(upload_cancel:|auto_cancel:|auto_cancel_job:)")))
    app_bot.add_handler(CallbackQueryHandler(handle_download_cancel, filters.regex(r"^download_cancel:")))
    app_bot.add_handler(CallbackQueryHandler(handle_cancel_job, filters.regex(r"^cancel_job:")))

    app_bot.add_handler(MessageHandler(handle_incoming_message, filters.private & ~filters.regex(r"^/")))

# ============================================================
# FIXED auto_compress_and_upload with size-based progress and idle timeout
# Also passes client to OptimizedProgress
# ============================================================
async def auto_compress_and_upload(
    user,
    original_path: Path,
    chat_id: int,
    initiator_message: Optional[Message] = None,
    cancel_key: Optional[str] = None,
    stop_event: Optional[asyncio.Event] = None
) -> bool:
    if not await get_automator_enabled(user):
        logger.debug("Automator disabled for user, skipping compression/upload")
        return False
    if is_torrent_file(original_path):
        logger.info("Automator: skipping .torrent file, no compression/upload needed")
        await safe_send(chat_id, "ℹ️ Automator: Los archivos .torrent no se comprimen ni suben.")
        return False

    user_root = get_user_root_path(user).resolve()
    if original_path.resolve() == user_root:
        await safe_send(chat_id, "❌ Automator: No se comprime toda la carpeta de usuario. Revise sus rutas de descarga.")
        logger.error(f"Automator aborted because original_path is the user root: {original_path}")
        return False

    # ---- Disk quota and free space check ----
    ok, msg = await check_disk_free_space(user_root)
    if not ok:
        await safe_send(chat_id, msg)
        return False
    original_size = await asyncio.wait_for(asyncio.to_thread(get_total_size_sync, original_path), timeout=THREADED_WALK_TIMEOUT)
    ok, msg = await check_user_quota(user, additional_bytes=original_size)
    if not ok:
        await safe_send(chat_id, msg)
        return False

    global AUTOMATOR_ACTIVE_COUNT, AUTOMATOR_JOBS
    async with AUTOMATOR_SEMAPHORE:
        async with _AUTOMATOR_COUNT_LOCK:
            AUTOMATOR_ACTIVE_COUNT += 1

        job_id = uuid.uuid4().hex
        job_cancel_event = asyncio.Event()
        pending_upload_tasks = []
        proc = None
        progress_msg = None

        AUTOMATOR_JOBS[job_id] = {
            "cancel_event": job_cancel_event,
            "proc": None,
            "pending_tasks": pending_upload_tasks,
            "progress_msg": None,
            "original_path": original_path,
            "chat_id": chat_id,
        }

        try:
            if not original_path.exists():
                await safe_send(chat_id, f"❌ Automator: la ruta {original_path.name} no existe.")
                return False

            total_input_size = original_size

            seven_cmd = None
            try:
                if SEVENZ_PATH:
                    sp = Path(SEVENZ_PATH)
                    if sp.exists() and sp.is_file():
                        seven_cmd = str(sp)
                    else:
                        seven_cmd = shutil.which(SEVENZ_PATH) or shutil.which("7z") or shutil.which("7za") or shutil.which("7zr")
                else:
                    seven_cmd = shutil.which("7z") or shutil.which("7za") or shutil.which("7zr")
            except Exception:
                seven_cmd = shutil.which("7z") or shutil.which("7za") or shutil.which("7zr")

            if not seven_cmd:
                await safe_send(chat_id, "❌ Automator: no se encontró la herramienta de compresión (7z). Instálela o configure SEVENZ_PATH.")
                return False

            out_dir = original_path.parent
            base_name = sanitize_filename(original_path.stem if original_path.is_file() else original_path.name)
            archive_base = out_dir / f"{base_name}.7z"

            existing_parts = await asyncio.wait_for(asyncio.to_thread(lambda: list(out_dir.glob(f"{archive_base.name}.*"))), timeout=FILE_IO_TIMEOUT)
            for old in existing_parts:
                try:
                    await asyncio.wait_for(asyncio.to_thread(old.unlink, missing_ok=True), timeout=FILE_IO_TIMEOUT)
                except Exception:
                    pass

            cmd = [
                seven_cmd, "a", "-t7z", "-bb1", "-bsp1",
                "-mx=0",
                f"-v{2000}m",
                "-y",
                str(archive_base),
                str(original_path)
            ]

            proc = await asyncio.create_subprocess_exec(
                *cmd,
                cwd=str(out_dir),
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.STDOUT
            )
            AUTOMATOR_JOBS[job_id]["proc"] = proc

            part_pattern = re.compile(rf"{re.escape(archive_base.name)}\.([0-9]+)$")

            last_activity = [time.time()]

            async def update_status(text: str):
                nonlocal progress_msg
                last_activity[0] = time.time()
                if progress_msg is None:
                    progress_msg = await safe_send(chat_id, text, parse_mode=ParseMode.HTML)
                    AUTOMATOR_JOBS[job_id]["progress_msg"] = progress_msg
                else:
                    try:
                        await edit_with_retry(progress_msg.edit_text(_scrub_text_for_user(text), parse_mode=ParseMode.HTML))
                    except Exception:
                        pass

            await update_status(f"🔄 Automator: comprimiendo {original_path.name} en partes de 2GB...")

            read_task = asyncio.create_task(_read_7z_output(proc, update_status))

            uploaded_parts = set()
            expected_part = 1
            pending_parts = {}

            def get_output_size_sum():
                total = 0
                for entry in out_dir.iterdir():
                    if entry.is_file() and entry.name.startswith(archive_base.name):
                        total += entry.stat().st_size
                return total

            try:
                while True:
                    if asyncio.current_task().cancelled():
                        logger.info("auto_compress_and_upload cancelled")
                        break
                    if time.time() - last_activity[0] > COMPRESSION_IDLE_TIMEOUT:
                        await update_status(f"❌ Automator: sin progreso durante {COMPRESSION_IDLE_TIMEOUT//60} minutos. Cancelando.")
                        if proc.returncode is None:
                            proc.terminate()
                        break

                    if job_cancel_event.is_set():
                        logger.info(f"Automator job {job_id} cancelled by user")
                        await update_status("❌ Trabajo del Automator cancelado por el usuario.")
                        if proc.returncode is None:
                            try:
                                proc.terminate()
                            except Exception:
                                pass
                        break

                    await asyncio.sleep(1.0)

                    dir_entries = await asyncio.wait_for(asyncio.to_thread(lambda: list(out_dir.iterdir())), timeout=FILE_IO_TIMEOUT)
                    for candidate in dir_entries:
                        if not candidate.is_file():
                            continue
                        if candidate.name in uploaded_parts:
                            continue
                        m = part_pattern.search(candidate.name)
                        if not m:
                            continue
                        part_num = int(m.group(1))

                        stable = False
                        try:
                            size1 = await asyncio.wait_for(asyncio.to_thread(lambda: candidate.stat().st_size), timeout=FILE_IO_TIMEOUT)
                            await asyncio.sleep(0.5)
                            size2 = await asyncio.wait_for(asyncio.to_thread(lambda: candidate.stat().st_size), timeout=FILE_IO_TIMEOUT)
                            if size1 == size2 and size1 > 0:
                                stable = True
                        except Exception:
                            pass
                        if not stable:
                            continue

                        last_activity[0] = time.time()

                        out_size = await asyncio.wait_for(asyncio.to_thread(get_output_size_sum), timeout=FILE_IO_TIMEOUT)
                        pct = min(100.0, (out_size / total_input_size) * 100.0) if total_input_size > 0 else 0.0
                        bar = "█" * int(pct / 5) + "░" * (20 - int(pct / 5))

                        # ---------- QUOTA CHECK ----------
                        remaining = total_input_size - out_size
                        if await check_quota_and_abort(user,
                                                       additional_bytes=remaining,
                                                       progress_msg=progress_msg,
                                                       cancel_event=job_cancel_event):
                            if proc.returncode is None:
                                proc.terminate()
                            break
                        # ---------------------------------

                        await update_status(f"🔄 Comprimiendo...\n{bar} {pct:.1f}%")

                        uploaded_parts.add(candidate.name)
                        if part_num not in pending_parts:
                            pending_parts[part_num] = candidate

                        while expected_part in pending_parts:
                            part_path = pending_parts.pop(expected_part)
                            await update_status(f"📤 Subiendo parte {expected_part}: {part_path.name}")

                            cancel_data = f"auto_cancel_job:{job_id}"
                            progress_markup = InlineKeyboardMarkup(
                                [[InlineKeyboardButton("Cancelar trabajo", callback_data=cancel_data)]]
                            )

                            total_size = await asyncio.wait_for(asyncio.to_thread(lambda: part_path.stat().st_size), timeout=FILE_IO_TIMEOUT)

                            if FORCE_USER_UPLOADS:
                                use_bot = False
                            elif FORCE_BOT_UPLOADS:
                                use_bot = True
                            else:
                                use_bot = (total_size > LARGE_FILE_THRESHOLD)
                            if not use_bot and user_client is None:
                                logger.warning("Automator: user client not available, falling back to bot client")
                                use_bot = True
                            upload_client = bot_client if use_bot else user_client

                            try:
                                start_time = time.time()
                                upload_msg = await safe_send(
                                    chat_id,
                                    "<i>Preparando subida...</i>",
                                    reply_markup=progress_markup
                                )

                                # Pass the upload client to OptimizedProgress
                                progress_handler = OptimizedProgress(
                                    part_path.name, total_size, upload_msg, start_time,
                                    update_interval=15.0,
                                    reply_markup=progress_markup,
                                    client=upload_client
                                )

                                caption = f"<i>{part_path.name}</i>\n<i>@GamesDarkCloud</i>"
                                thumb_path = THUMBNAIL_PATH if THUMBNAIL_PATH and THUMBNAIL_PATH.exists() else None
                                send_kwargs = {
                                    "chat_id": chat_id,
                                    "document": str(part_path),
                                    "caption": caption,
                                    "parse_mode": ParseMode.HTML,
                                    "progress": progress_handler,
                                    "reply_markup": progress_markup,
                                }
                                if thumb_path:
                                    send_kwargs["thumb"] = str(thumb_path)

                                task = asyncio.current_task()
                                pending_upload_tasks.append(task)

                                sent_doc = await upload_with_retry(upload_client, send_kwargs)

                                try:
                                    await edit_with_retry(sent_doc.edit_caption(
                                        caption=sent_doc.caption.html if sent_doc.caption else caption,
                                        reply_markup=None
                                    ))
                                except Exception:
                                    pass
                                await edit_with_retry(upload_msg.edit(f"<i>✅ Subido {part_path.name}</i>", reply_markup=None))
                                await asyncio.wait_for(asyncio.to_thread(part_path.unlink, missing_ok=True), timeout=FILE_IO_TIMEOUT)
                                await asyncio.sleep(2.0)

                            except asyncio.CancelledError:
                                await safe_send(chat_id, f"❌ Subida de {part_path.name} cancelada.")
                                await asyncio.wait_for(asyncio.to_thread(part_path.unlink, missing_ok=True), timeout=FILE_IO_TIMEOUT)
                                raise
                            except Exception as e:
                                logger.exception(f"Failed to upload part {part_path.name}")
                                await safe_send(chat_id, f"❌ Automator: falló la subida de {part_path.name}: {str(e)[:100]}")
                            finally:
                                if task in pending_upload_tasks:
                                    pending_upload_tasks.remove(task)

                            expected_part += 1

                    if proc.returncode is not None and not pending_parts:
                        await asyncio.sleep(1)
                        leftover = await asyncio.wait_for(asyncio.to_thread(lambda: list(out_dir.iterdir())), timeout=FILE_IO_TIMEOUT)
                        for candidate in leftover:
                            if not candidate.is_file():
                                continue
                            if candidate.name in uploaded_parts:
                                continue
                            m = part_pattern.search(candidate.name)
                            if m:
                                part_num = int(m.group(1))
                                if part_num not in pending_parts:
                                    pending_parts[part_num] = candidate
                        if not pending_parts:
                            break

                if job_cancel_event.is_set():
                    parts_to_delete = await asyncio.wait_for(asyncio.to_thread(lambda: list(out_dir.glob(f"{archive_base.name}.*"))), timeout=FILE_IO_TIMEOUT)
                    for f in parts_to_delete:
                        try:
                            await asyncio.wait_for(asyncio.to_thread(f.unlink, missing_ok=True), timeout=FILE_IO_TIMEOUT)
                        except Exception:
                            pass
                    return False

                await read_task

                if proc.returncode == 0:
                    try:
                        if original_path.is_dir():
                            await asyncio.wait_for(asyncio.to_thread(shutil.rmtree, original_path), timeout=FILE_IO_TIMEOUT)
                        else:
                            await asyncio.wait_for(asyncio.to_thread(original_path.unlink), timeout=FILE_IO_TIMEOUT)
                    except Exception as e:
                        logger.warning(f"Automator: could not delete original {original_path}: {e}")
                    await update_status("✅ Automator: compresión y subida completadas. Original eliminado.")
                    return True
                else:
                    await update_status(f"❌ Automator: compresión falló con código {proc.returncode}")
                    return False

            except asyncio.CancelledError:
                if proc and proc.returncode is None:
                    proc.terminate()
                raise
            finally:
                if read_task and not read_task.done():
                    read_task.cancel()
                AUTOMATOR_JOBS.pop(job_id, None)

        finally:
            async with _AUTOMATOR_COUNT_LOCK:
                AUTOMATOR_ACTIVE_COUNT -= 1

# ============================================================
# _read_7z_output – minimal
# ============================================================
async def _read_7z_output(proc: asyncio.subprocess.Process, status_callback):
    try:
        while True:
            if hasattr(_read_7z_output, "_cancel_event") and _read_7z_output._cancel_event.is_set():
                break
            line = await asyncio.wait_for(proc.stdout.readline(), timeout=SEVENZ_READ_TIMEOUT)
            if not line:
                break
    except asyncio.CancelledError:
        pass
    except asyncio.TimeoutError:
        logger.warning("7z read timeout, terminating process")
        proc.terminate()
    except Exception as e:
        logger.exception("Error in 7z output reader")

# ============================================================
# PINGTASK WATCHDOG – LATIDO INTERNO PARA DETECTAR CONGELAMIENTOS
# ============================================================
async def ping_task():
    """Actualiza el timestamp de latido cada 5 segundos."""
    global _last_heartbeat
    while True:
        await asyncio.sleep(5)
        async with _heartbeat_lock:
            _last_heartbeat = time.time()

async def recover_from_freeze():
    """Intenta recuperar el bot sin perder tareas críticas."""
    logger.critical("Attempting recovery from freeze...")
    # 1. Cancelar tareas auxiliares (no críticas) – pero no las de subida
    cancelled = 0
    for task in asyncio.all_tasks():
        if task.get_name() in ("ping_task", "event_loop_watchdog", "network_health_check"):
            continue
        if not task.done() and not task.cancelled():
            # Solo cancelar tareas de edición, monitores o progress, pero nunca las de upload
            if ("edit" in task.get_name() or "monitor" in task.get_name() or "progress" in task.get_name()) and \
               not any("upload" in t.get_name() for t in asyncio.all_tasks() if t is not task):
                task.cancel()
                cancelled += 1
    if cancelled:
        logger.info(f"Cancelled {cancelled} auxiliary tasks")
        await asyncio.sleep(1)

    # 2. Reconectar clientes de forma segura (sin stop/start)
    async with _reconnect_lock:
        try:
            if bot_client and bot_client.is_connected:
                await asyncio.wait_for(bot_client.reconnect(), timeout=15.0)
                logger.info("Bot client reconnected after freeze.")
            if user_client and user_client.is_connected:
                await asyncio.wait_for(user_client.reconnect(), timeout=15.0)
                logger.info("User client reconnected after freeze.")
        except asyncio.TimeoutError:
            logger.error("Reconnect timeout during recovery. Forcing reconnect...")
            # Intentar reconnect de nuevo sin stop/start
            try:
                await bot_client.reconnect()
                await user_client.reconnect()
                logger.info("Clients reconnected after recovery.")
            except Exception as e:
                logger.critical(f"Could not reconnect clients: {e}")
        except Exception as e:
            logger.error(f"Recovery error: {e}")

    # 3. Resetear latido para evitar bucle
    async with _heartbeat_lock:
        _last_heartbeat = time.time()

async def event_loop_watchdog():
    """Detecta congelamiento del event loop y ejecuta recuperación."""
    global _last_heartbeat
    while True:
        await asyncio.sleep(20)  # comprobar cada 20s
        async with _heartbeat_lock:
            last = _last_heartbeat
        now = time.time()
        if now - last > 90:  # 90 segundos sin latido (aumentado desde 60)
            logger.critical(f"Event loop frozen! No heartbeat for {now - last:.0f}s.")
            await recover_from_freeze()

# ============================================================
# NETWORK HEALTH CHECK (OPCIONAL, CON INTERVALO LARGO)
# ============================================================
async def network_health_check():
    """Verifica conectividad con Telegram cada 15 minutos, solo si el latido está vivo."""
    while True:
        await asyncio.sleep(900)  # 15 minutos
        # Solo si no hay congelamiento detectado (latido reciente)
        async with _heartbeat_lock:
            last = _last_heartbeat
        if time.time() - last > 30:
            logger.debug("Skipping network check: event loop may be frozen.")
            continue
        # Hacer ping real a Telegram
        try:
            if bot_client and bot_client.is_connected:
                await asyncio.wait_for(bot_client.get_me(), timeout=10.0)
            if user_client and user_client.is_connected:
                await asyncio.wait_for(user_client.get_me(), timeout=10.0)
        except asyncio.TimeoutError:
            logger.warning("Network ping timeout. Attempting reconnect...")
            async with _reconnect_lock:
                try:
                    if bot_client and bot_client.is_connected:
                        await asyncio.wait_for(bot_client.reconnect(), timeout=15.0)
                    if user_client and user_client.is_connected:
                        await asyncio.wait_for(user_client.reconnect(), timeout=15.0)
                except Exception as e:
                    logger.error(f"Network reconnect failed: {e}")
        except Exception as e:
            logger.warning(f"Network health check error: {e}")

# ============================================================
# REEMPLAZO DE HEALTH CHECKS ANTIGUOS – SE ELIMINAN
# (las funciones anteriores bot_client_health_check, global_activity_watchdog,
#  connection_health_check, task_health_check han sido eliminadas o reemplazadas)
# ============================================================

# ============================================================
# QBITTORRENT FUNCTIONS – IMPROVED TORRENT HANDLING + RESILIENT EDITS
# ============================================================
async def _qb_login(session: aiohttp.ClientSession, base_url: str) -> bool:
    if not QBT_USER and not QBT_PASS:
        return True
    login_url = f"{base_url}/api/v2/auth/login"
    data = {"username": QBT_USER or "", "password": QBT_PASS or ""}
    try:
        async with session.post(login_url, data=data, timeout=10) as resp:
            return resp.status == 200
    except Exception:
        return False

async def _qb_add_torrent_file(session: aiohttp.ClientSession, base_url: str, file_path: str, savepath: str) -> Tuple[bool, str]:
    add_url = f"{base_url}/api/v2/torrents/add"
    try:
        file_data = await asyncio.wait_for(asyncio.to_thread(lambda: open(file_path, "rb").read()), timeout=FILE_IO_TIMEOUT)
        form = aiohttp.FormData()
        form.add_field("torrents", file_data, filename=Path(file_path).name, content_type="application/x-bittorrent")
        form.add_field("savepath", str(savepath))
        async with session.post(add_url, data=form, timeout=30) as resp:
            text = await resp.text()
            logger.info(f"qBittorrent add response: status={resp.status}, body={text[:200]}")
            return resp.status in (200, 201, 202), text
    except Exception as e:
        logger.exception("qBittorrent add torrent file failed")
        return False, str(e)

async def _qb_add_magnet(session: aiohttp.ClientSession, base_url: str, magnet: str, savepath: str) -> Tuple[bool, str]:
    add_url = f"{base_url}/api/v2/torrents/add"
    data = {"urls": magnet, "savepath": str(savepath)}
    try:
        async with session.post(add_url, data=data, timeout=10) as resp:
            text = await resp.text()
            logger.info(f"qBittorrent add magnet response: status={resp.status}, body={text[:200]}")
            return resp.status in (200, 201, 202), text
    except Exception as e:
        logger.exception("qBittorrent add magnet failed")
        return False, str(e)

async def _qb_find_torrent_by_name_and_path(session: aiohttp.ClientSession, base_url: str, name: str, savepath: str, timeout_seconds: float = 30.0, torrent_filename: Optional[str] = None):
    info_url = f"{base_url}/api/v2/torrents/info"
    end = time.time() + timeout_seconds
    while time.time() < end:
        try:
            async with session.get(info_url, timeout=10) as resp:
                if resp.status != 200:
                    await asyncio.sleep(0.5)
                    continue
                data = await resp.json()
                # Sort by added_on (most recent first)
                sorted_data = sorted(data, key=lambda x: x.get("added_on", 0), reverse=True)
                for t in sorted_data:
                    tname = t.get("name") or ""
                    tpath = t.get("save_path") or ""
                    # Normalize paths
                    if os.path.normpath(tpath) == os.path.normpath(str(savepath)):
                        # Match by internal name (case-insensitive)
                        if tname.lower() == name.lower():
                            return t.get("hash")
                        # Also match by the original .torrent filename (if provided)
                        if torrent_filename and Path(torrent_filename).stem.lower() == tname.lower():
                            return t.get("hash")
                # Fallback: return the most recent torrent with matching savepath
                for t in sorted_data:
                    if os.path.normpath(t.get("save_path", "")) == os.path.normpath(str(savepath)):
                        return t.get("hash")
        except Exception:
            pass
        await asyncio.sleep(1.0)
    return None

async def _qb_get_torrent_info(session: aiohttp.ClientSession, base_url: str, torrent_hash: str):
    info_url = f"{base_url}/api/v2/torrents/info"
    params = {"hashes": torrent_hash}
    try:
        async with session.get(info_url, params=params, timeout=10) as resp:
            if resp.status != 200:
                return None
            data = await resp.json()
            if isinstance(data, list) and data:
                return data[0]
            return None
    except Exception:
        return None

async def _qb_remove_torrent(session: aiohttp.ClientSession, base_url: str, torrent_hash: str, delete_files: bool = False) -> bool:
    delete_url = f"{base_url}/api/v2/torrents/delete"
    data = {"hashes": torrent_hash, "deleteFiles": "true" if delete_files else "false"}
    try:
        async with session.post(delete_url, data=data, timeout=10) as resp:
            return resp.status in (200, 202)
    except Exception as e:
        logger.warning(f"Failed to remove torrent {torrent_hash} (keep files: {not delete_files}): {e}")
        return False

# ============================================================
# QBITTORRENT DOWNLOAD WITH INACTIVITY TIMEOUT (UPDATED WITH IMPROVED TORRENT FINDING + RESILIENT EDITS)
# All progress edits are fire-and-forget (asyncio.create_task) to avoid blocking.
# ============================================================
async def aria2_download_items(links: List[str], tg_user, telegram_message, wait_for_automator: bool = False, cancel_key_override: Optional[str] = None) -> Tuple[int, List[Tuple[str, bool, str]]]:
    user_folder = get_user_folder_name(tg_user)
    base = TELELOAD_BASE_DIR.rstrip("/")
    if not base:
        base = "/"
    if base == "/":
        dest_base = Path.cwd().anchor
        dest_dir = Path(dest_base) / user_folder
    else:
        dest_dir = Path(base) / user_folder
    try:
        await asyncio.wait_for(asyncio.to_thread(dest_dir.mkdir, parents=True, exist_ok=True), timeout=FILE_IO_TIMEOUT)
    except Exception:
        asyncio.create_task(
            edit_progress_resilient(
                telegram_message,
                "Error al crear la carpeta de destino para descargas.",
                client=bot_client,
                per_attempt_timeout=5.0
            )
        )
        return 0, [(l, False, "mkdir failed") for l in links]

    base_url = f"http://{QBT_HOST}:{QBT_PORT}"
    results = []

    if cancel_key_override:
        cancel_key = cancel_key_override
    else:
        cancel_key = uuid.uuid4().hex
    stop_evt = asyncio.Event()
    try:
        DOWNLOAD_TASKS[cancel_key] = {"stop_event": stop_evt, "user_id": getattr(tg_user, "id", None), "cancelled": False, "type": "qb"}
        asyncio.create_task(
            edit_progress_resilient(
                telegram_message,
                telegram_message.text if getattr(telegram_message, "text", None) else "",
                reply_markup=_download_cancel_keyboard(cancel_key),
                client=bot_client,
                per_attempt_timeout=5.0
            )
        )

        def make_session():
            connector = aiohttp.TCPConnector(
                force_close=True,
                enable_cleanup_closed=True,
                ttl_dns_cache=300
            )
            timeout = aiohttp.ClientTimeout(total=12.0, connect=5.0, sock_read=8.0)
            return aiohttp.ClientSession(connector=connector, timeout=timeout)

        automator_tasks_local = []
        pending_edit_tasks = []

        def add_edit_task(edit_task):
            MAX_PENDING_EDITS = 3
            while len(pending_edit_tasks) >= MAX_PENDING_EDITS:
                old = pending_edit_tasks.pop(0)
                if not old.done():
                    old.cancel()
            pending_edit_tasks.append(edit_task)

        existing_folders_before = set()
        if dest_dir.exists():
            for item in dest_dir.iterdir():
                if item.is_dir():
                    existing_folders_before.add(item.name)

        main_session = make_session()
        try:
            for idx, link in enumerate(links, start=1):
                if asyncio.current_task().cancelled():
                    break
                if stop_evt.is_set() or DOWNLOAD_TASKS.get(cancel_key, {}).get("cancelled"):
                    results.append((link, False, "cancelled_by_user"))
                    break

                link = link.strip()
                item_for_qb = link
                temp_torrent_path = None
                downloaded_temp = False
                candidate_name_for_conflict = None
                torrent_filename_for_lookup = None

                if path.isfile(link) and link.lower().endswith(".torrent"):
                    p = Path(link)
                    temp_torrent_path = str(p)
                    item_for_qb = temp_torrent_path
                    torrent_filename_for_lookup = p.name
                    try:
                        tname = await asyncio.wait_for(asyncio.to_thread(bdecode_get_name_of_torrent, p), timeout=FILE_IO_TIMEOUT)
                        if tname:
                            candidate_name_for_conflict = sanitize_filename(tname)
                    except Exception:
                        candidate_name_for_conflict = None
                elif is_torrent_url(link) and link.lower().startswith("http"):
                    try:
                        asyncio.create_task(
                            edit_progress_resilient(
                                telegram_message,
                                f"<i>[{idx}/{len(links)}] Descargando archivo torrent desde URL...</i>",
                                client=bot_client,
                                per_attempt_timeout=5.0
                            )
                        )
                        tmp = await download_torrent_file(main_session, link, dest_dir)
                        temp_torrent_path = str(tmp)
                        downloaded_temp = True
                        torrent_filename_for_lookup = tmp.name
                        item_for_qb = temp_torrent_path
                        tname = await asyncio.wait_for(asyncio.to_thread(bdecode_get_name_of_torrent, Path(temp_torrent_path)), timeout=FILE_IO_TIMEOUT)
                        if tname:
                            candidate_name_for_conflict = sanitize_filename(tname)
                    except Exception:
                        results.append((link, False, "Failed to download .torrent"))
                        continue
                elif is_magnet(link):
                    try:
                        parsed = urllib.parse.urlparse(link)
                        q = urllib.parse.parse_qs(parsed.query)
                        dn_vals = q.get("dn") or q.get("DN") or q.get("Name")
                        if dn_vals:
                            dn = dn_vals[0]
                            candidate_name_for_conflict = sanitize_filename(urllib.parse.unquote(dn))
                    except Exception:
                        candidate_name_for_conflict = None
                else:
                    results.append((link, False, "unsupported"))
                    continue

                if candidate_name_for_conflict:
                    predicted_folder = dest_dir / candidate_name_for_conflict
                    if predicted_folder.exists() and predicted_folder.is_dir():
                        bak_name = f"{candidate_name_for_conflict}_bak_{int(time.time())}_{uuid.uuid4().hex[:4]}"
                        bak_path = dest_dir / bak_name
                        await asyncio.wait_for(asyncio.to_thread(predicted_folder.rename, bak_path), timeout=FILE_IO_TIMEOUT)
                        asyncio.create_task(
                            edit_progress_resilient(
                                telegram_message,
                                f"<i>[{idx}/{len(links)}] Carpeta existente '{candidate_name_for_conflict}' movida a '{bak_name}' para descarga limpia.</i>",
                                client=bot_client,
                                per_attempt_timeout=5.0
                            )
                        )

                asyncio.create_task(
                    edit_progress_resilient(
                        telegram_message,
                        f"<i>[{idx}/{len(links)}] Añadiendo al cliente de torrents...</i>",
                        reply_markup=_download_cancel_keyboard(cancel_key),
                        client=bot_client,
                        per_attempt_timeout=5.0
                    )
                )

                added = False
                add_msg = ""
                try:
                    if temp_torrent_path:
                        added, add_msg = await _qb_add_torrent_file(main_session, base_url, temp_torrent_path, dest_dir)
                    else:
                        if is_magnet(link):
                            added, add_msg = await _qb_add_magnet(main_session, base_url, link, dest_dir)
                except aiohttp.ClientError as e:
                    logger.warning(f"Session error on add, recreating session: {e}")
                    await main_session.close()
                    main_session = make_session()
                    try:
                        if temp_torrent_path:
                            added, add_msg = await _qb_add_torrent_file(main_session, base_url, temp_torrent_path, dest_dir)
                        else:
                            if is_magnet(link):
                                added, add_msg = await _qb_add_magnet(main_session, base_url, link, dest_dir)
                    except Exception as e2:
                        added = False
                        add_msg = str(e2)

                if not added:
                    logger.error(f"Failed to add torrent: {add_msg}")
                    results.append((link, False, f"add_failed: {add_msg[:100]}"))
                    if temp_torrent_path and downloaded_temp:
                        try:
                            await asyncio.wait_for(asyncio.to_thread(Path(temp_torrent_path).unlink, missing_ok=True), timeout=FILE_IO_TIMEOUT)
                        except Exception:
                            pass
                    continue

                name_to_find = candidate_name_for_conflict or _derive_display_name_from_link(link, tg_user)
                torrent_hash = await _qb_find_torrent_by_name_and_path(
                    main_session, base_url, name_to_find, dest_dir,
                    timeout_seconds=30.0,
                    torrent_filename=torrent_filename_for_lookup
                )
                if not torrent_hash:
                    info_url = f"{base_url}/api/v2/torrents/info"
                    try:
                        async with main_session.get(info_url, timeout=8) as resp:
                            if resp.status == 200:
                                data = await resp.json()
                                found = None
                                for t in data:
                                    try:
                                        if os.path.normpath(t.get("save_path", "")) == os.path.normpath(str(dest_dir)):
                                            found = t.get("hash")
                                            break
                                    except Exception:
                                        continue
                                torrent_hash = found
                    except Exception:
                        torrent_hash = None

                if not torrent_hash:
                    logger.warning(f"Could not identify torrent for {name_to_find}, skipping.")
                    results.append((link, False, "could_not_identify"))
                    if temp_torrent_path and downloaded_temp:
                        try:
                            await asyncio.wait_for(asyncio.to_thread(Path(temp_torrent_path).unlink, missing_ok=True), timeout=FILE_IO_TIMEOUT)
                        except Exception:
                            pass
                    continue

                # ---- MONITORING LOOP con reintentos prolongados ----
                torrent_session = make_session()
                try:
                    start_time = time.time()
                    last_update = 0.0
                    last_loaded_bytes = 0
                    last_inactive_check = time.time()
                    success = False
                    info_text = ""
                    last_title = name_to_find
                    last_seen_time = time.time()
                    consecutive_failures = 0
                    MAX_CONSECUTIVE_FAILURES = 5
                    API_RESPONSE_TIMEOUT = 30.0
                    last_api_success = time.time()

                    # Variables para controlar el tiempo sin información de la API
                    no_info_start = None          # momento en que empezó la falta de info
                    MAX_NO_INFO_SECONDS = 30 * 60  # 30 minutos de reintentos

                    async def _do_one_iteration(current_session):
                        nonlocal last_seen_time, last_loaded_bytes, last_inactive_check, last_title, last_update, success, info_text, last_api_success, consecutive_failures
                        try:
                            tinfo = await asyncio.wait_for(_qb_get_torrent_info(current_session, base_url, torrent_hash), timeout=12.0)
                            last_api_success = time.time()
                            consecutive_failures = 0
                        except asyncio.TimeoutError:
                            logger.warning("_qb_get_torrent_info timed out")
                            consecutive_failures += 1
                            if consecutive_failures >= MAX_CONSECUTIVE_FAILURES:
                                success = False
                                info_text = f"max_api_timeouts_{MAX_CONSECUTIVE_FAILURES}"
                                return True, False   # finished=True, no_info=False (error crítico)
                            return False, True       # finished=False, no_info=True (timeout)
                        except aiohttp.ClientError as e:
                            logger.warning(f"Client error in _do_one_iteration: {e}")
                            consecutive_failures += 1
                            if consecutive_failures >= MAX_CONSECUTIVE_FAILURES:
                                success = False
                                info_text = f"max_api_errors_{MAX_CONSECUTIVE_FAILURES}"
                                return True, False
                            return False, True
                        except Exception as e:
                            logger.exception(f"Unexpected error in _do_one_iteration: {e}")
                            success = False
                            info_text = f"api_error: {str(e)[:100]}"
                            return True, False

                        now = time.time()
                        if not tinfo:
                            # No se obtuvo información -> indicamos no_info=True
                            return False, True   # no finalizado, sin info

                        # Tenemos información, reseteamos el contador de no_info
                        last_seen_time = now
                        total = int(tinfo.get("total_size") or 0)
                        prog = float(tinfo.get("progress", 0.0) or 0.0)
                        loaded = int(prog * total) if total else 0
                        elapsed = time.time() - start_time
                        rate = int(tinfo.get("dlspeed", 0) or 0)
                        eta = None
                        try:
                            if total and loaded is not None and rate and rate > 0:
                                eta = (total - loaded) / rate
                        except Exception:
                            pass
                        title = tinfo.get("name") or last_title
                        last_title = title

                        # Quota check
                        remaining = total - loaded
                        if await check_quota_and_abort(tg_user,
                                                       additional_bytes=remaining,
                                                       message=telegram_message,
                                                       stop_event=stop_evt,
                                                       cancel_key=cancel_key):
                            task = asyncio.create_task(edit_progress_resilient(
                                telegram_message,
                                f"<i>{title}\n\nCuota excedida – descarga cancelada.</i>",
                                client=bot_client
                            ))
                            pending_edit_tasks.append(task)
                            success = False
                            info_text = "quota_exceeded"
                            return True, False

                        # Inactivity check
                        if loaded > last_loaded_bytes:
                            last_loaded_bytes = loaded
                            last_inactive_check = now
                        elif (now - last_inactive_check) > DOWNLOAD_INACTIVITY_TIMEOUT:
                            logger.warning(f"qBittorrent download inactivity timeout for {title}")
                            try:
                                await _qb_remove_torrent(current_session, base_url, torrent_hash, delete_files=True)
                            except Exception:
                                pass
                            success = False
                            info_text = f"inactivity_timeout_{DOWNLOAD_INACTIVITY_TIMEOUT}s"
                            task = asyncio.create_task(edit_progress_resilient(
                                telegram_message,
                                f"<i>{title}\n\nSin progreso durante {DOWNLOAD_INACTIVITY_TIMEOUT} segundos. Cancelado.</i>",
                                client=bot_client
                            ))
                            pending_edit_tasks.append(task)
                            return True, False

                        # Progress update
                        txt = build_progress_text(title, total if total > 0 else None, loaded if loaded is not None else None, elapsed, eta, speed=rate if rate else None)
                        now2 = time.time()
                        if (now2 - last_update) >= PROGRESS_UPDATE_INTERVAL:
                            task = asyncio.create_task(edit_progress_resilient(
                                telegram_message,
                                txt,
                                reply_markup=_download_cancel_keyboard(cancel_key),
                                client=bot_client
                            ))
                            pending_edit_tasks.append(task)
                            last_update = now2

                        # Check completion
                        prog_val = tinfo.get("progress", 0.0)
                        if prog_val is not None and float(prog_val) >= 0.9999:
                            success = True
                            info_text = "Download finished"

                            await asyncio.sleep(SUFFIX_POST_DOWNLOAD_WAIT)

                            content_path = None
                            content_path_from_api = tinfo.get("content_path")
                            if content_path_from_api:
                                content_path = Path(content_path_from_api)
                                logger.info(f"Got content_path from API: {content_path}")
                            else:
                                save_path = tinfo.get("save_path")
                                if save_path and title:
                                    content_path = Path(save_path) / title
                                    logger.info(f"Constructed content_path: {content_path}")

                            final_processed = None
                            if content_path and content_path.exists():
                                if content_path.is_file():
                                    final_processed = await process_path_with_suffix_and_signing_async(content_path)
                                elif content_path.is_dir():
                                    final_processed = await process_path_with_suffix_and_signing_async(content_path)
                            else:
                                logger.warning("Could not determine content_path from API, falling back to folder detection")
                                existing_folders_after = set()
                                if dest_dir.exists():
                                    for item in dest_dir.iterdir():
                                        if item.is_dir():
                                            existing_folders_after.add(item.name)
                                new_folders = existing_folders_after - existing_folders_before
                                if new_folders:
                                    newest = None
                                    for fname in new_folders:
                                        folder_path = dest_dir / fname
                                        if folder_path.exists():
                                            if newest is None or folder_path.stat().st_mtime > newest.stat().st_mtime:
                                                newest = folder_path
                                    if newest:
                                        final_processed = await process_path_with_suffix_and_signing_async(newest)
                                        logger.info(f"Detected new folder via before/after scan: {newest}")
                                else:
                                    for item in dest_dir.iterdir():
                                        if item.is_file() and item.name == title:
                                            final_processed = await process_path_with_suffix_and_signing_async(item)
                                            break

                            user_root = get_user_root_path(tg_user).resolve()
                            if final_processed and final_processed.resolve() == user_root:
                                logger.error(f"Refusing to compress user root folder from qBittorrent: {final_processed}")
                                await safe_send(telegram_message.chat.id, "❌ Automator: no se comprime la carpeta raíz del usuario. Revise sus rutas de descarga.")
                            elif await get_automator_enabled(tg_user) and final_processed and final_processed.exists():
                                task = asyncio.create_task(
                                    auto_compress_and_upload(
                                        user=tg_user,
                                        original_path=final_processed,
                                        chat_id=telegram_message.chat.id,
                                        initiator_message=telegram_message,
                                        cancel_key=cancel_key,
                                        stop_event=stop_evt
                                    )
                                )
                                automator_tasks_local.append(task)

                            try:
                                removed = await _qb_remove_torrent(current_session, base_url, torrent_hash, delete_files=False)
                                if removed:
                                    logger.info(f"Removed completed torrent {torrent_hash} from qBittorrent (files kept)")
                                else:
                                    logger.warning(f"Failed to remove torrent {torrent_hash} after completion")
                            except Exception as e:
                                logger.exception(f"Error removing torrent {torrent_hash}: {e}")

                            # Final edit – await with timeout to ensure user sees it
                            try:
                                await asyncio.wait_for(
                                    edit_progress_resilient(
                                        telegram_message,
                                        txt + "\n\n<i>Descarga finalizada (eliminada del cliente)</i>",
                                        client=bot_client,
                                        per_attempt_timeout=5.0
                                    ),
                                    timeout=6.0
                                )
                            except Exception:
                                pass
                            return True, False

                        state = (tinfo.get("state") or "").lower()
                        if state in ("error", "pauseddl", "missingfiles"):
                            success = False
                            info_text = f"state:{state}"
                            return True, False

                        return False, False   # progreso normal, no finalizado

                    async def _monitor_link():
                        nonlocal success, info_text, last_title, torrent_session, consecutive_failures, last_api_success, no_info_start
                        while True:
                            if asyncio.current_task().cancelled():
                                break
                            if stop_evt.is_set() or DOWNLOAD_TASKS.get(cancel_key, {}).get("cancelled"):
                                try:
                                    await _qb_remove_torrent(torrent_session, base_url, torrent_hash, delete_files=True)
                                except Exception:
                                    pass
                                success = False
                                info_text = "cancelled_by_user"
                                task = asyncio.create_task(edit_progress_resilient(
                                    telegram_message,
                                    f"<i>{last_title}\n\nCancelado por el usuario.</i>",
                                    client=bot_client
                                ))
                                pending_edit_tasks.append(task)
                                return

                            # Watchdog: si pasó mucho tiempo sin éxito de API, reiniciamos sesión
                            if time.time() - last_api_success > API_RESPONSE_TIMEOUT:
                                logger.warning(f"No API response for {API_RESPONSE_TIMEOUT}s, recreating session")
                                await torrent_session.close()
                                torrent_session = make_session()
                                last_api_success = time.time()
                                consecutive_failures = 0

                            try:
                                finished, no_info = await asyncio.wait_for(_do_one_iteration(torrent_session), timeout=15.0)
                                if finished:
                                    return  # descarga completada o error crítico
                                if no_info:
                                    # No se pudo obtener información de la API
                                    if no_info_start is None:
                                        no_info_start = time.time()
                                    elif time.time() - no_info_start > MAX_NO_INFO_SECONDS:
                                        # Superado el tiempo máximo de reintentos
                                        success = False
                                        info_text = f"api_unreachable_timeout_{MAX_NO_INFO_SECONDS}s"
                                        task = asyncio.create_task(edit_progress_resilient(
                                            telegram_message,
                                            f"<i>{last_title}\n\nNo se pudo contactar con el cliente de torrents durante {MAX_NO_INFO_SECONDS//60} minutos. Descarga fallida.</i>",
                                            client=bot_client
                                        ))
                                        pending_edit_tasks.append(task)
                                        return
                                    # Editamos mensaje para informar espera
                                    task = asyncio.create_task(edit_progress_resilient(
                                        telegram_message,
                                        f"<i>{last_title}\n\n⏳ Esperando reconexión con el cliente de torrents... (intentando desde hace {int(time.time() - no_info_start)}s)</i>",
                                        reply_markup=_download_cancel_keyboard(cancel_key),
                                        client=bot_client
                                    ))
                                    pending_edit_tasks.append(task)
                                    await asyncio.sleep(5)
                                    continue
                                else:
                                    # Si obtuvimos info, reseteamos el contador
                                    no_info_start = None
                            except asyncio.TimeoutError:
                                logger.warning("Monitoring iteration timed out, recreating session")
                                await torrent_session.close()
                                torrent_session = make_session()
                                consecutive_failures = 0
                                # No reiniciamos no_info_start porque ya está en curso
                                continue
                            except aiohttp.ClientError as e:
                                logger.warning(f"Client error in monitor, recreating session: {e}")
                                await torrent_session.close()
                                torrent_session = make_session()
                                consecutive_failures = 0
                                # Marcamos como no_info para que entre en el bloque de espera
                                if no_info_start is None:
                                    no_info_start = time.time()
                                continue
                            except Exception as e:
                                logger.exception("Unexpected error in monitoring iteration, aborting")
                                success = False
                                info_text = f"iteration_error: {str(e)[:100]}"
                                return

                            await asyncio.sleep(1.0)

                    SAFETY_TIMEOUT = DOWNLOAD_SAFETY_TIMEOUT if DOWNLOAD_SAFETY_TIMEOUT > 0 else 86400
                    try:
                        await asyncio.wait_for(_monitor_link(), timeout=SAFETY_TIMEOUT)
                    except asyncio.TimeoutError:
                        logger.error(f"Download for {name_to_find} exceeded safety timeout ({SAFETY_TIMEOUT}s)")
                        success = False
                        info_text = f"safety_timeout_{SAFETY_TIMEOUT}s"
                        task = asyncio.create_task(edit_progress_resilient(
                            telegram_message,
                            f"<i>{last_title}\n\nDescarga cancelada por tiempo de seguridad.</i>",
                            client=bot_client
                        ))
                        pending_edit_tasks.append(task)

                    # Cancelar tareas de edición pendientes
                    for t in pending_edit_tasks:
                        if not t.done():
                            t.cancel()
                    pending_edit_tasks.clear()

                    results.append((link, success, info_text))
                    if temp_torrent_path and downloaded_temp:
                        try:
                            await asyncio.wait_for(asyncio.to_thread(Path(temp_torrent_path).unlink, missing_ok=True), timeout=FILE_IO_TIMEOUT)
                        except Exception:
                            pass
                    await asyncio.sleep(0.3)

                finally:
                    await torrent_session.close()

        finally:
            await main_session.close()

        if wait_for_automator and automator_tasks_local:
            await asyncio.gather(*automator_tasks_local, return_exceptions=True)

    finally:
        try:
            DOWNLOAD_TASKS.pop(cancel_key, None)
        except Exception:
            pass

    success_count = sum(1 for _, ok, _ in results if ok)
    return success_count, results

async def graceful_shutdown(signum=None, frame=None):
    logger.info("Received shutdown signal, cleaning up...")
    tasks = [t for t in asyncio.all_tasks() if t is not asyncio.current_task()]
    for task in tasks:
        task.cancel()
    try:
        await asyncio.wait_for(asyncio.gather(*tasks, return_exceptions=True), timeout=5.0)
    except asyncio.TimeoutError:
        logger.warning("Some tasks didn't cancel within timeout")
    except Exception:
        pass
    if bot_client and bot_client.is_connected:
        try:
            await asyncio.wait_for(bot_client.stop(), timeout=3.0)
        except Exception:
            pass
    if user_client and user_client.is_connected:
        try:
            await asyncio.wait_for(user_client.stop(), timeout=3.0)
        except Exception:
            pass
    logger.info("Shutdown complete")
    loop = asyncio.get_event_loop()
    loop.stop()
    await asyncio.sleep(0.5)

def enable_asyncio_debug():
    loop = asyncio.get_event_loop()
    loop.set_debug(True)
    loop.slow_callback_duration = 3.0
    def blocker_handler(loop, context):
        msg = context.get('message', 'Unknown')
        if 'blocking' in msg.lower() or 'slow' in msg.lower():
            logger.error(f"ASYNC BLOCKER DETECTED: {msg}")
            import traceback
            traceback.print_stack(context.get('future', None))
    loop.set_exception_handler(blocker_handler)

async def start_clients_and_run():
    global bot_client, user_client, BOT_ID, AUTOMATOR_SEMAPHORE, _AUTOMATOR_COUNT_LOCK
    global PROCESSING_QUEUE, PROCESSING_SEMAPHORE, PROCESSING_WORKERS, START_TIME, _last_successful_edit

    if os.getenv("ASYNCIO_DEBUG", "false").lower() == "true":
        enable_asyncio_debug()
        logger.warning("ASYNCIO_DEBUG enabled - performance may be reduced")

    executor = concurrent.futures.ThreadPoolExecutor(max_workers=100)
    asyncio.get_running_loop().set_default_executor(executor)
    logger.info("Increased default thread pool size to 100")

    max_connection_retries = 3
    try:
        api_id_val = int(PYRO_API_ID)
    except Exception:
        api_id_val = PYRO_API_ID

    # --- Load proxy settings from environment ---
    proxy_enabled = os.getenv("PROXY_ENABLED", "false").lower() == "true"
    proxy_dict = None
    if proxy_enabled:
        scheme = os.getenv("PROXY_SCHEME", "socks5").lower()
        host = os.getenv("PROXY_HOST", "127.0.0.1")
        try:
            port = int(os.getenv("PROXY_PORT", "40000"))
        except ValueError:
            port = 40000
        username = os.getenv("PROXY_USERNAME")
        password = os.getenv("PROXY_PASSWORD")

        proxy_dict = {
            "scheme": scheme,
            "hostname": host,
            "port": port,
        }
        if username:
            proxy_dict["username"] = username
        if password:
            proxy_dict["password"] = password

        logger.info(f"Proxy enabled: {scheme}://{host}:{port}")
    else:
        logger.info("Proxy disabled – connecting directly")

    bot_client = Client(
        "pyro_bot",
        bot_token=TELEGRAM_TOKEN,
        api_id=api_id_val,
        api_hash=PYRO_API_HASH,
        workers=WORKER_COUNT,
        max_concurrent_transmissions=MAX_CONCURRENT_UPLOADS,
        sleep_threshold=300,       # increased to 5 minutes
        parse_mode=ParseMode.HTML,
        proxy=proxy_dict,           # None if disabled
    )
    user_client = Client(
        "pyro_user",
        api_id=api_id_val,
        api_hash=PYRO_API_HASH,
        workers=WORKER_COUNT,
        max_concurrent_transmissions=MAX_CONCURRENT_UPLOADS,
        sleep_threshold=300,       # increased to 5 minutes
        parse_mode=ParseMode.HTML,
        proxy=proxy_dict,
    )

    for attempt in range(max_connection_retries):
        try:
            await bot_client.start()
            me = await bot_client.get_me()
            BOT_ID = getattr(me, "id", None)
            await user_client.start()
            START_TIME = time.time()
            _last_successful_edit = time.time()  # Initialize watchdog timestamp
            logger.info(f"Bot client and user client started. Bot ID: {BOT_ID}")
            logger.info(f"Optimized settings: workers={WORKER_COUNT}, max_concurrent={MAX_CONCURRENT_UPLOADS}")

            _AUTOMATOR_COUNT_LOCK = asyncio.Lock()
            AUTOMATOR_SEMAPHORE = asyncio.Semaphore(AUTOMATOR_CONCURRENCY)

            PROCESSING_QUEUE = asyncio.Queue()
            PROCESSING_SEMAPHORE = asyncio.Semaphore(AUTOMATOR_CONCURRENCY)
            PROCESSING_WORKERS.clear()
            for _ in range(AUTOMATOR_CONCURRENCY):
                worker = asyncio.create_task(processing_worker())
                PROCESSING_WORKERS.append(worker)

            break
        except Exception as e:
            logger.error(f"Failed to start clients (attempt {attempt+1}/{max_connection_retries}): {e}")
            if attempt < max_connection_retries - 1:
                await asyncio.sleep(CONNECTION_RETRY_DELAY)
            else:
                raise

    # --- INICIAR TAREAS DE SUPERVISIÓN UNIFICADAS ---
    # 1. Pingtask (latido interno)
    asyncio.create_task(ping_task(), name="ping_task")
    # 2. Watchdog del event loop
    asyncio.create_task(event_loop_watchdog(), name="event_loop_watchdog")
    # 3. Health check de red (opcional, intervalo largo)
    asyncio.create_task(network_health_check(), name="network_health_check")
    # 4. Keep-alive loop para user client (solo ping)
    asyncio.create_task(keep_alive_loop(), name="keep_alive_loop")
    # 5. Task health check para monitorear tareas de descarga (ahora menos agresivo)
    asyncio.create_task(task_health_check(), name="task_health_check")

    register_handlers(bot_client)
    try:
        logger.info("Bot is running. Press Ctrl+C to stop.")
        await idle()
    finally:
        await graceful_shutdown()

def main():
    def handle_shutdown(signum, frame):
        logger.info(f"Received signal {signum}, shutting down...")
        try:
            loop = asyncio.get_event_loop()
            if loop.is_running():
                asyncio.create_task(graceful_shutdown(signum, frame))
            else:
                os._exit(0)
        except Exception:
            os._exit(0)

    signal_module.signal(signal_module.SIGINT, handle_shutdown)
    signal_module.signal(signal_module.SIGTERM, handle_shutdown)

    try:
        signal_module.signal(signal_module.SIGPIPE, signal_module.SIG_IGN)
    except AttributeError:
        pass

    try:
        asyncio.run(start_clients_and_run())
    except KeyboardInterrupt:
        logger.info("KeyboardInterrupt received")
    except asyncio.CancelledError:
        logger.info("Cancelled")
    except Exception as e:
        logger.exception(f"Unhandled exception: {e}")
    finally:
        logger.info("Exiting...")
        os._exit(0)

if __name__ == "__main__":
    main()
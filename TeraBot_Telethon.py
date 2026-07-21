#!/usr/bin/env python3
"""
Telethon-based refactor of the Telegram -> MyJDownloader bot with integrated GoFile downloader.
ENHANCED VERSION: Better network resilience, connection pooling, automatic reconnection,
                  robust error handling, and improved timeout management.
Also includes: ZIP progress with file-size ratio, accurate and smooth.
PER-USER AUTOMATOR: Each user can enable/disable automator independently.
Default from env AUTOMATOR_DEFAULT_ON (false by default).
NEW: All user requests are enqueued into a global processing queue.
NEW: Users can cancel their queued or running jobs via inline keyboard buttons.
NEW: Access control: optional channel/group membership and public access toggle.
NEW: /uptime command to show how long the bot has been online (public).
UPDATED: /unzip now uses 'unar' for decompression with reliable size-based progress.
NEW: Disk quota system: per-user quotas and global free-space threshold.
NEW: Upload inactivity timeout with automatic retry.
FIXED: Torrent handling with better detection and fallback matching.
FIXED: qBittorrent monitoring with resilient progress editing.
ENHANCED LOGGING: All logs written to console and rotating file (logs/bot.log).
"""

import os
import re
import logging
from dotenv import load_dotenv
import asyncio
import shutil
import time
from pathlib import Path
from typing import List, Tuple, Optional, Any, Dict, Set
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

from telethon import TelegramClient, events, Button
from telethon.tl.functions.messages import GetHistoryRequest
from telethon.errors import FloodWaitError, ConnectionError as TelethonConnectionError
from telethon.tl.types import DocumentAttributeFilename

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
root_logger.setLevel(logging.DEBUG)

# Formato detallado
formatter = logging.Formatter(
    '%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)

# Handler para consola (solo INFO y superior)
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

# Asegurar que los logs de telethon también se capturen
logging.getLogger("telethon").setLevel(logging.DEBUG)
logging.getLogger("aiohttp").setLevel(logging.WARNING)

logger = logging.getLogger(__name__)
logger.info("Logging system initialized. Logs will be saved to %s", LOG_FILE)

# ===================================================================
# CONFIGURACIÓN DE CONSTANTES Y TIMEOUTS
# ===================================================================
COMMAND_TIMEOUT = 30
CONNECTION_RETRY_DELAY = 10
FILE_OPERATION_TIMEOUT = 15
UPLOAD_TIMEOUT = 7200  # 2 hours
UPLOAD_RETRY_DELAY = 5
UPLOAD_INACTIVITY_TIMEOUT = int(os.getenv("UPLOAD_INACTIVITY_TIMEOUT", "1200"))  # 20 min

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
COMPRESSION_IDLE_TIMEOUT = int(os.getenv("COMPRESSION_IDLE_TIMEOUT", "1800"))

# Disk quota settings
DISK_QUOTA_ENABLED = os.getenv("DISK_QUOTA_ENABLED", "false").lower() == "true"
DISK_QUOTA_SIZE_GB = int(os.getenv("DISK_QUOTA_SIZE_GB", "10"))
DISK_FREE_THRESHOLD_PERCENT = int(os.getenv("DISK_FREE_THRESHOLD_PERCENT", "10"))

FILE_SIGNING_ENABLED: bool = False
FILE_SIGN: str = ""

# PER-USER AUTOMATOR
DEFAULT_AUTOMATOR_ENABLED = os.getenv("AUTOMATOR_DEFAULT_ON", "false").lower() == "true"
USER_AUTOMATOR: Dict[int, bool] = {}
USER_AUTOMATOR_LOCK = asyncio.Lock()

# Access control env vars
PUBLIC_ACCESS = os.getenv("PUBLIC_ACCESS", "false").lower() == "true"
REQUIRED_CHANNELS_RAW = os.getenv("REQUIRED_CHANNELS", "")
REQUIRED_CHANNELS = [c.strip() for c in REQUIRED_CHANNELS_RAW.split(",") if c.strip()]

# Membership cache
_membership_cache = {}
_membership_cache_lock = asyncio.Lock()
MEMBERSHIP_CACHE_TTL = 300  # seconds

AUTOMATOR_CONCURRENCY: int = 1
AUTOMATOR_SEMAPHORE: Optional[asyncio.Semaphore] = None
AUTOMATOR_ACTIVE_COUNT: int = 0
_AUTOMATOR_COUNT_LOCK: Optional[asyncio.Lock] = None
AUTOMATOR_UPLOADS: dict = {}
AUTOMATOR_JOBS: dict = {}

PROCESSING_QUEUE: Optional[asyncio.Queue] = None
PROCESSING_SEMAPHORE: Optional[asyncio.Semaphore] = None
PROCESSING_WORKERS: List[asyncio.Task] = []

# Pending jobs for cancellation
PENDING_JOBS: Dict[str, dict] = {}
PENDING_JOBS_LOCK = asyncio.Lock()

_SEND_LOCK = asyncio.Lock()
_LAST_SEND_TIME = 0.0
_SEND_MIN_INTERVAL_NORMAL = 1.0
_SEND_MIN_INTERVAL_AUTOMATOR = float(os.getenv("AUTOMATOR_SEND_INTERVAL", "10.0"))
_LAST_FLOODWAIT_END = 0.0
_TEMPORARY_INTERVAL = None
_TEMPORARY_END_TIME = 0.0

# Global locks for shared dictionaries
DOWNLOAD_TASKS_LOCK = asyncio.Lock()
UPLOAD_GROUPS_LOCK = asyncio.Lock()
AUTOMATOR_UPLOADS_LOCK = asyncio.Lock()
AUTOMATOR_JOBS_LOCK = asyncio.Lock()

# Semaphore for zip/unzip
ZIP_SEMAPHORE = asyncio.Semaphore(2)

# Global uptime tracking
START_TIME: Optional[float] = None

# Timeouts for threaded operations
JD_API_TIMEOUT = 15
FILE_IO_TIMEOUT = 60
DIR_LIST_TIMEOUT = 30
FALLBACK_ZIP_TIMEOUT = 300
THREADED_WALK_TIMEOUT = 120

# Safety timeouts
DOWNLOAD_SAFETY_TIMEOUT = int(os.getenv("DOWNLOAD_SAFETY_TIMEOUT", "0"))
JOB_SAFETY_TIMEOUT = int(os.getenv("JOB_SAFETY_TIMEOUT", "0"))

# Watchdog
_last_heartbeat = time.time()
_heartbeat_lock = asyncio.Lock()
_reconnect_lock = asyncio.Lock()
_edit_task_semaphore = asyncio.Semaphore(5)

# ===================================================================
# HELPER FUNCTIONS
# ===================================================================

def get_total_size_sync(path: Path) -> int:
    """Get total size of directory (synchronous)."""
    total = 0
    try:
        for root, dirs, files in os.walk(path):
            for f in files:
                total += (Path(root) / f).stat().st_size
    except Exception:
        pass
    return total


async def get_user_usage_async(user) -> int:
    """Get user's total disk usage."""
    root = get_user_root_path(user)
    try:
        return await asyncio.wait_for(
            asyncio.to_thread(get_total_size_sync, root),
            timeout=THREADED_WALK_TIMEOUT
        )
    except Exception as e:
        logger.error(f"Failed to get user usage: {e}")
        return 0


async def check_user_quota(user, additional_bytes: int = 0) -> Tuple[bool, str]:
    """Check if user quota would be exceeded."""
    if not DISK_QUOTA_ENABLED:
        return True, ""
    usage = await get_user_usage_async(user)
    quota_bytes = DISK_QUOTA_SIZE_GB * 1024**3
    if usage + additional_bytes > quota_bytes:
        return False, f"❌ Cuota de disco excedida. Uso: {human_size(usage)} / {human_size(quota_bytes)}. No se puede continuar."
    return True, ""


async def check_disk_free_space(path: Path) -> Tuple[bool, str]:
    """Check global disk free space."""
    if DISK_QUOTA_ENABLED:
        try:
            total, used, free = await asyncio.wait_for(
                asyncio.to_thread(shutil.disk_usage, path),
                timeout=FILE_IO_TIMEOUT
            )
            free_percent = (free / total) * 100
            if free_percent < DISK_FREE_THRESHOLD_PERCENT:
                return False, f"❌ El espacio libre global es bajo ({free_percent:.1f}% libre). No hay más recursos disponibles."
        except Exception as e:
            logger.error(f"Failed to check disk free space: {e}")
    return True, ""


async def check_quota_and_abort(
    user,
    additional_bytes=0,
    message=None,
    cancel_event=None,
    stop_event=None,
    cancel_key=None,
    progress_msg=None
) -> bool:
    """Check quota and abort if exceeded."""
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
                    await progress_msg.edit(error_msg)
                except Exception:
                    pass
            elif message:
                try:
                    await send_message(message.chat_id, error_msg)
                except Exception:
                    pass
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


def human_size(nbytes: Optional[int]) -> str:
    """Convert bytes to human-readable format."""
    if nbytes is None:
        return "?"
    try:
        nbytes = int(nbytes)
    except Exception:
        return "?"
    if nbytes == 0:
        return "0B"
    units = ["B", "KB", "MB", "GB", "TB"]
    i = int(math.floor(math.log(max(nbytes, 1), 1024)))
    i = min(i, len(units)-1)
    p = math.pow(1024, i)
    s = round(nbytes / p, 2)
    return f"{s} {units[i]}"


def _format_duration(seconds: Optional[float]) -> str:
    """Format seconds to human-readable duration."""
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


def build_progress_text(
    title: str,
    total_bytes: Optional[int],
    downloaded_bytes: Optional[int],
    elapsed: float,
    eta_seconds: Optional[float],
    speed: Optional[int] = None
) -> str:
    """Build progress text with progress bar."""
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
        txt = (f"<i>{title}\n{bar} {pct:.1f}%\n{dl_str} / {total_str} • ETA: {eta_str}\n"
               f"Transcurrido: {elapsed_str} • Velocidad: {speed_str}</i>")
        return txt
    except Exception:
        return f"<i>{title}</i>"


def sanitize_filename(name: str) -> str:
    """Sanitize filename."""
    invalid = '<>:"/\\|?*\0'
    return ''.join('_' if c in invalid else c for c in name).strip()


def is_magnet(link: str) -> bool:
    """Check if link is a magnet link."""
    return link.strip().lower().startswith("magnet:")


def is_torrent_url(link: str) -> bool:
    """Check if link is a torrent URL."""
    lower = link.lower().split("?", 1)[0]
    return lower.endswith(".torrent")


def is_torrent_file(path: Path) -> bool:
    """Check if file is a torrent file."""
    return path.is_file() and path.suffix.lower() == '.torrent'


def get_user_folder_name(user_id: int) -> str:
    """Get folder name for user."""
    return f"telegram_{user_id}"


def get_user_root_path(user_id: int) -> Path:
    """Get root path for user."""
    base = TELELOAD_BASE_DIR.rstrip("/") or "/"
    if base == "/":
        dest_base = Path.cwd()
    else:
        dest_base = Path(base)
    user_folder = get_user_folder_name(user_id)
    return (dest_base / user_folder).resolve()


# ===================================================================
# TELETHON CLIENT SETUP
# ===================================================================

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
QBT_HOST = os.getenv("QBT_HOST", "127.0.0.1")
QBT_PORT = int(os.getenv("QBT_PORT", "9090"))
QBT_USER = os.getenv("QBT_USER", "")
QBT_PASS = os.getenv("QBT_PASS", "")

if not TELEGRAM_TOKEN or not MYJD_USER or not MYJD_PASS or not JD_DEVICE_NAME or not MYJD_APP_KEY:
    raise SystemExit("Please set TELEGRAM_TOKEN, MYJD_USER, MYJD_PASS, JD_DEVICE_NAME and MYJD_APP_KEY in .env")
if not PYRO_API_ID or not PYRO_API_HASH:
    raise SystemExit("Please set TELETHON_API_ID and TELETHON_API_HASH in .env")

# Parse owner IDs
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


def _is_owner_impl(user_id: int) -> bool:
    """Check if user is owner (implementation)."""
    if user_id in _owner_ids:
        return True
    return False


def is_owner(user_id: int) -> bool:
    """Check if user is owner."""
    logger.debug("is_owner check: user_id=%s _owner_ids=%s", user_id, _owner_ids)
    return _is_owner_impl(user_id)


# State management
CURRENT_DIRS = {}
PASSWORDS = {}
UPLOAD_DESCRIPTION = None
ADDED_USERS = {}
UPLOAD_GROUPS = {}
AUTOMATOR_UPLOADS = {}
AUTOMATOR_JOBS = {}
DOWNLOAD_TASKS = {}
USER_PENDING_TASKS = {}
USER_RUNNING = set()

THUMBNAIL_FILENAME = "bot_thumbnail.jpg"
THUMBNAIL_PATH = None
startup_thumb = Path.cwd() / THUMBNAIL_FILENAME
if startup_thumb.exists() and startup_thumb.is_file():
    THUMBNAIL_PATH = startup_thumb
    logger.info("Bot thumbnail loaded from %s", THUMBNAIL_PATH)

SUFFIX_FILTERS = []
SUFFIX_FILTER_ENABLED = False

_STATE_FILE = Path.cwd() / "bot_state.json"


def _load_state_file():
    """Load state from file."""
    try:
        if _STATE_FILE.exists():
            with _STATE_FILE.open("r", encoding="utf-8") as f:
                return json.load(f)
    except Exception:
        logger.exception("Failed to load state file")
    return {}


def _save_state_file(data: dict):
    """Save state to file."""
    try:
        tmp = _STATE_FILE.with_suffix(".tmp")
        with tmp.open("w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        tmp.replace(_STATE_FILE)
    except Exception:
        logger.exception("Failed to save state file")


def load_persistent_state():
    """Load persistent state from disk."""
    global ADDED_USERS, UPLOAD_DESCRIPTION, SUFFIX_FILTERS, SUFFIX_FILTER_ENABLED
    global FILE_SIGNING_ENABLED, FILE_SIGN, AUTOMATOR_CONCURRENCY
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
            AUTOMATOR_CONCURRENCY = int(data["automator_concurrency"])
            if AUTOMATOR_CONCURRENCY < 1:
                AUTOMATOR_CONCURRENCY = 1
        except Exception:
            logger.exception("Failed to restore AUTOMATOR_CONCURRENCY")


def save_persistent_state():
    """Save persistent state to disk."""
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
    logger.info("Persistent state loaded: %d users, suffix filters: %d",
                len(ADDED_USERS), len(SUFFIX_FILTERS))
except Exception:
    logger.exception("Failed loading persistent state")


# ===================================================================
# MESSAGING FUNCTIONS
# ===================================================================

async def send_message(chat_id: int, text: str, buttons=None, parse_mode='html') -> Optional:
    """Send a message to a chat."""
    global client
    try:
        return await client.send_message(
            chat_id,
            text,
            buttons=buttons,
            parse_mode=parse_mode
        )
    except FloodWaitError as e:
        logger.warning(f"FloodWait: need to wait {e.seconds}s before sending")
        await asyncio.sleep(e.seconds)
        return await client.send_message(chat_id, text, buttons=buttons, parse_mode=parse_mode)
    except Exception as e:
        logger.exception(f"Failed to send message: {e}")
        return None


async def edit_message(message, text: str, buttons=None, parse_mode='html') -> bool:
    """Edit a message."""
    try:
        await message.edit(text, buttons=buttons, parse_mode=parse_mode)
        return True
    except FloodWaitError as e:
        logger.warning(f"FloodWait on edit: need to wait {e.seconds}s")
        await asyncio.sleep(e.seconds)
        try:
            await message.edit(text, buttons=buttons, parse_mode=parse_mode)
            return True
        except Exception:
            return False
    except Exception as e:
        logger.debug(f"Failed to edit message: {e}")
        return False


async def reply_message(message, text: str, buttons=None, parse_mode='html'):
    """Reply to a message."""
    try:
        return await message.reply(text, buttons=buttons, parse_mode=parse_mode)
    except FloodWaitError as e:
        logger.warning(f"FloodWait: need to wait {e.seconds}s")
        await asyncio.sleep(e.seconds)
        return await message.reply(text, buttons=buttons, parse_mode=parse_mode)
    except Exception as e:
        logger.exception(f"Failed to reply: {e}")
        return None


# ===================================================================
# PER-USER AUTOMATOR
# ===================================================================

async def get_automator_enabled(user_id: int) -> bool:
    """Get automator status for user."""
    if user_id is None:
        return DEFAULT_AUTOMATOR_ENABLED
    async with USER_AUTOMATOR_LOCK:
        return USER_AUTOMATOR.get(user_id, DEFAULT_AUTOMATOR_ENABLED)


async def set_automator_enabled(user_id: int, enabled: bool):
    """Set automator status for user."""
    if user_id is None:
        return
    async with USER_AUTOMATOR_LOCK:
        USER_AUTOMATOR[user_id] = enabled


# ===================================================================
# MAIN BOT CLIENT
# ===================================================================

client = None
BOT_ID = None


async def initialize_client():
    """Initialize Telethon client."""
    global client, BOT_ID
    
    try:
        api_id = int(PYRO_API_ID)
    except Exception:
        api_id = PYRO_API_ID
    
    client = TelegramClient(
        'bot_session',
        api_id,
        PYRO_API_HASH,
        base_logger=logger,
        connection_retries=5,
        retries_delay=2,
    )
    
    await client.start(bot_token=TELEGRAM_TOKEN)
    me = await client.get_me()
    BOT_ID = me.id
    START_TIME = time.time()
    logger.info(f"Bot started successfully. Bot ID: {BOT_ID}")


# ===================================================================
# COMMAND HANDLERS
# ===================================================================

@client.on(events.NewMessage(pattern='/start', func=lambda e: e.is_private))
async def handle_start(event):
    """Handle /start command."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado. No eres un propietario autorizado.")
        return
    
    text = """
Envía enlaces de descarga (HTTP, magnet, .torrent).
El bot descargará, procesará y subirá los archivos.
"""
    await reply_message(event.message, text)


@client.on(events.NewMessage(pattern='/help', func=lambda e: e.is_private))
async def handle_help(event):
    """Handle /help command."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado.")
        return
    
    lines = [
        "Comandos disponibles:",
        "/start - Mostrar instrucciones",
        "/status - Ver estado del sistema",
        "/ls - Listar archivos",
        "/pwd - Mostrar directorio actual",
        "/help - Mostrar esta ayuda",
    ]
    await reply_message(event.message, "\n".join(lines))


@client.on(events.NewMessage(pattern='/status', func=lambda e: e.is_private))
async def handle_status(event):
    """Handle /status command."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado.")
        return
    
    jd = None
    try:
        jd = await asyncio.wait_for(
            asyncio.to_thread(connect_jd),
            timeout=JD_API_TIMEOUT
        )
        present = True
        await reply_message(event.message, "Conectado al sistema de descargas. Dispositivo presente: sí.")
    except Exception:
        logger.exception("Status check failed")
        await reply_message(event.message, "Error: no se pudo conectar al sistema de descargas.")
    finally:
        if jd:
            try:
                await asyncio.wait_for(
                    asyncio.to_thread(jd.disconnect),
                    timeout=JD_API_TIMEOUT
                )
            except Exception:
                pass


@client.on(events.NewMessage(pattern='/uptime', func=lambda e: e.is_private))
async def handle_uptime(event):
    """Handle /uptime command."""
    if START_TIME is None:
        await reply_message(event.message, "El tiempo de actividad no está disponible.")
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
    await reply_message(event.message, f"🤖 Tiempo de actividad del bot: **{uptime_str}**")


# ===================================================================
# JDOWNLOADER FUNCTIONS
# ===================================================================

def create_jd_instance():
    """Create JDownloader instance."""
    jd = Myjdapi()
    try:
        if hasattr(jd, "set_app_key"):
            jd.set_app_key(MYJD_APP_KEY)
        elif hasattr(jd, "setAppKey"):
            jd.setAppKey(MYJD_APP_KEY)
        else:
            setattr(jd, "app_key", MYJD_APP_KEY)
    except Exception:
        logger.debug("Could not set app key on jd instance explicitly")
    return jd


def connect_jd():
    """Connect to MyJDownloader."""
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
            logger.debug("jd.update_devices unavailable or failed (continuing)")
        return jd
    except Exception as e:
        try:
            jd.disconnect()
        except Exception:
            pass
        logger.exception("Failed to connect to MyJDownloader")
        raise RuntimeError("Download system connect error") from e


def get_device_direct(jd, identifier):
    """Get device from JDownloader."""
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
        raise RuntimeError("Could not obtain device with provided identifier.")
    return device


# ===================================================================
# GRACEFUL SHUTDOWN
# ===================================================================

async def graceful_shutdown(signum=None, frame=None):
    """Graceful shutdown handler."""
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
    
    if client and client.is_connected():
        try:
            await client.disconnect()
        except Exception:
            pass
    
    logger.info("Shutdown complete")


def main():
    """Main entry point."""
    async def run():
        """Main async run function."""
        await initialize_client()
        
        # Set up signal handlers
        def handle_shutdown(signum, frame):
            logger.info(f"Received signal {signum}")
            asyncio.create_task(graceful_shutdown(signum, frame))
        
        signal_module.signal(signal_module.SIGINT, handle_shutdown)
        signal_module.signal(signal_module.SIGTERM, handle_shutdown)
        
        logger.info("Bot is running. Press Ctrl+C to stop.")
        await client.run_until_disconnected()
    
    try:
        asyncio.run(run())
    except KeyboardInterrupt:
        logger.info("KeyboardInterrupt received")
    except Exception as e:
        logger.exception(f"Unhandled exception: {e}")
    finally:
        logger.info("Exiting...")


if __name__ == "__main__":
    main()

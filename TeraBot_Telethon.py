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
    global client, BOT_ID, START_TIME
    
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
# COMMAND HANDLERS - BASIC
# ===================================================================

@client.on(events.NewMessage(pattern='/start', func=lambda e: e.is_private))
async def handle_start(event):
    """Handle /start command."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado. No eres un propietario autorizado.")
        return
    
    text = """
<b>🤖 TeraBot - Sistema de Descargas Inteligente</b>

Envía enlaces de descarga:
• 🌐 HTTP/HTTPS (enlaces directos)
• 🧲 Magnet links (torrents)
• 📦 .torrent files

El bot descargará, procesará y subirá los archivos automáticamente.

<b>Comandos disponibles:</b>
/help - Ver todos los comandos
/status - Estado del sistema
/uptime - Tiempo de actividad
"""
    await reply_message(event.message, text)


@client.on(events.NewMessage(pattern='/help', func=lambda e: e.is_private))
async def handle_help(event):
    """Handle /help command."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado.")
        return
    
    lines = [
        "<b>📋 Comandos Disponibles:</b>",
        "",
        "<b>Información:</b>",
        "/start - Instrucciones iniciales",
        "/status - Estado del sistema",
        "/uptime - Tiempo de actividad del bot",
        "/help - Esta ayuda",
        "",
        "<b>Gestión de Archivos:</b>",
        "/ls - Listar archivos en directorio actual",
        "/pwd - Mostrar directorio actual",
        "/cd &lt;path&gt; - Cambiar directorio",
        "/mkdir &lt;name&gt; - Crear carpeta",
        "/rm &lt;name&gt; - Eliminar archivo/carpeta",
        "/mv &lt;old&gt; &lt;new&gt; - Mover/renombrar",
        "/cp &lt;src&gt; &lt;dst&gt; - Copiar",
        "",
        "<b>Compresión:</b>",
        "/zip &lt;name&gt; - Comprimir en ZIP",
        "/unzip &lt;name&gt; - Descomprimir",
        "",
        "<b>Automator:</b>",
        "/automator_on - Activar compresión automática",
        "/automator_off - Desactivar compresión automática",
        "/automator_status - Ver estado automator",
        "",
        "<b>Descarga:</b>",
        "Envía URL, magnet o .torrent para descargar",
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
        await reply_message(event.message, "✅ Sistema de descargas: <b>Conectado</b>\n\n🤖 Telethon: <b>Activo</b>\n\nTodo funcionando correctamente.")
    except Exception as e:
        logger.exception("Status check failed")
        await reply_message(event.message, f"❌ Error: {str(e)}\n\nVerifica la conexión a JDownloader.")
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
    await reply_message(event.message, f"🤖 Tiempo de actividad del bot: <b>{uptime_str}</b>")


# ===================================================================
# COMMAND HANDLERS - FILE MANAGEMENT
# ===================================================================

@client.on(events.NewMessage(pattern='/pwd', func=lambda e: e.is_private))
async def handle_pwd(event):
    """Handle /pwd command."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado.")
        return
    
    user_id = event.sender_id
    user_root = get_user_root_path(user_id)
    current = CURRENT_DIRS.get(user_id, user_root)
    
    try:
        current = Path(current).resolve()
        await reply_message(event.message, f"<code>{current}</code>")
    except Exception as e:
        await reply_message(event.message, f"❌ Error: {str(e)}")


@client.on(events.NewMessage(pattern='/ls', func=lambda e: e.is_private))
async def handle_ls(event):
    """Handle /ls command."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado.")
        return
    
    user_id = event.sender_id
    user_root = get_user_root_path(user_id)
    current = CURRENT_DIRS.get(user_id, user_root)
    
    try:
        current = Path(current).resolve()
        user_root = user_root.resolve()
        
        # Security check
        if not str(current).startswith(str(user_root)):
            current = user_root
            CURRENT_DIRS[user_id] = current
        
        items = []
        if current != user_root:
            items.append("[↑ ..]")
        
        try:
            for item in sorted(current.iterdir()):
                try:
                    if item.is_dir():
                        items.append(f"📁 {item.name}/")
                    else:
                        size = item.stat().st_size
                        items.append(f"📄 {item.name} ({human_size(size)})")
                except Exception:
                    items.append(f"❓ {item.name}")
        except Exception as e:
            await reply_message(event.message, f"❌ Error al leer directorio: {str(e)}")
            return
        
        if not items:
            items = ["(directorio vacío)"]
        
        text = f"<code>{current}</code>\n\n" + "\n".join(items[:50])
        await reply_message(event.message, text)
    except Exception as e:
        logger.exception("ls error")
        await reply_message(event.message, f"❌ Error: {str(e)}")


@client.on(events.NewMessage(pattern=r'/cd\s+(.+)', func=lambda e: e.is_private))
async def handle_cd(event):
    """Handle /cd command."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado.")
        return
    
    user_id = event.sender_id
    user_root = get_user_root_path(user_id)
    current = CURRENT_DIRS.get(user_id, user_root)
    
    target = event.pattern_match.group(1).strip()
    
    try:
        current = Path(current).resolve()
        user_root = user_root.resolve()
        
        if target == "..":
            if current != user_root:
                current = current.parent
        elif target.startswith("/"):
            target_path = Path(target).resolve()
        else:
            target_path = (current / target).resolve()
        
        if target != ".." and not target.startswith("/"):
            target_path = (current / target).resolve()
        
        # Security check
        if not str(target_path).startswith(str(user_root)):
            await reply_message(event.message, "❌ Acceso denegado: fuera de directorio permitido.")
            return
        
        if not target_path.exists():
            await reply_message(event.message, "❌ Ruta no existe.")
            return
        
        if not target_path.is_dir():
            await reply_message(event.message, "❌ No es un directorio.")
            return
        
        CURRENT_DIRS[user_id] = target_path
        await reply_message(event.message, f"✅ Directorio cambiado a:\n<code>{target_path}</code>")
    except Exception as e:
        logger.exception("cd error")
        await reply_message(event.message, f"❌ Error: {str(e)}")


@client.on(events.NewMessage(pattern=r'/mkdir\s+(.+)', func=lambda e: e.is_private))
async def handle_mkdir(event):
    """Handle /mkdir command."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado.")
        return
    
    user_id = event.sender_id
    user_root = get_user_root_path(user_id)
    current = CURRENT_DIRS.get(user_id, user_root)
    
    name = event.pattern_match.group(1).strip()
    
    try:
        current = Path(current).resolve()
        user_root = user_root.resolve()
        
        new_dir = (current / name).resolve()
        
        # Security check
        if not str(new_dir).startswith(str(user_root)):
            await reply_message(event.message, "❌ Acceso denegado.")
            return
        
        new_dir.mkdir(parents=True, exist_ok=True)
        await reply_message(event.message, f"✅ Carpeta creada: <code>{new_dir.name}</code>")
    except Exception as e:
        logger.exception("mkdir error")
        await reply_message(event.message, f"❌ Error: {str(e)}")


@client.on(events.NewMessage(pattern=r'/rm\s+(.+)', func=lambda e: e.is_private))
async def handle_rm(event):
    """Handle /rm command."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado.")
        return
    
    user_id = event.sender_id
    user_root = get_user_root_path(user_id)
    current = CURRENT_DIRS.get(user_id, user_root)
    
    name = event.pattern_match.group(1).strip()
    
    try:
        current = Path(current).resolve()
        user_root = user_root.resolve()
        
        target = (current / name).resolve()
        
        # Security check
        if not str(target).startswith(str(user_root)):
            await reply_message(event.message, "❌ Acceso denegado.")
            return
        
        if not target.exists():
            await reply_message(event.message, "❌ No existe.")
            return
        
        if target.is_dir():
            await asyncio.wait_for(
                asyncio.to_thread(shutil.rmtree, target),
                timeout=FILE_IO_TIMEOUT
            )
        else:
            target.unlink()
        
        await reply_message(event.message, f"✅ Eliminado: <code>{target.name}</code>")
    except Exception as e:
        logger.exception("rm error")
        await reply_message(event.message, f"❌ Error: {str(e)}")


@client.on(events.NewMessage(pattern=r'/mv\s+(\S+)\s+(.+)', func=lambda e: e.is_private))
async def handle_mv(event):
    """Handle /mv command."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado.")
        return
    
    user_id = event.sender_id
    user_root = get_user_root_path(user_id)
    current = CURRENT_DIRS.get(user_id, user_root)
    
    old_name = event.pattern_match.group(1).strip()
    new_name = event.pattern_match.group(2).strip()
    
    try:
        current = Path(current).resolve()
        user_root = user_root.resolve()
        
        old_path = (current / old_name).resolve()
        new_path = (current / new_name).resolve()
        
        # Security check
        if (not str(old_path).startswith(str(user_root)) or
            not str(new_path).startswith(str(user_root))):
            await reply_message(event.message, "❌ Acceso denegado.")
            return
        
        if not old_path.exists():
            await reply_message(event.message, "❌ No existe.")
            return
        
        old_path.rename(new_path)
        await reply_message(event.message, f"✅ Movido/renombrado a: <code>{new_path.name}</code>")
    except Exception as e:
        logger.exception("mv error")
        await reply_message(event.message, f"❌ Error: {str(e)}")


@client.on(events.NewMessage(pattern=r'/cp\s+(\S+)\s+(.+)', func=lambda e: e.is_private))
async def handle_cp(event):
    """Handle /cp command."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado.")
        return
    
    user_id = event.sender_id
    user_root = get_user_root_path(user_id)
    current = CURRENT_DIRS.get(user_id, user_root)
    
    src_name = event.pattern_match.group(1).strip()
    dst_name = event.pattern_match.group(2).strip()
    
    try:
        current = Path(current).resolve()
        user_root = user_root.resolve()
        
        src_path = (current / src_name).resolve()
        dst_path = (current / dst_name).resolve()
        
        # Security check
        if (not str(src_path).startswith(str(user_root)) or
            not str(dst_path).startswith(str(user_root))):
            await reply_message(event.message, "❌ Acceso denegado.")
            return
        
        if not src_path.exists():
            await reply_message(event.message, "❌ No existe.")
            return
        
        if src_path.is_dir():
            await asyncio.wait_for(
                asyncio.to_thread(shutil.copytree, src_path, dst_path),
                timeout=FILE_IO_TIMEOUT
            )
        else:
            await asyncio.wait_for(
                asyncio.to_thread(shutil.copy2, src_path, dst_path),
                timeout=FILE_IO_TIMEOUT
            )
        
        await reply_message(event.message, f"✅ Copiado a: <code>{dst_path.name}</code>")
    except Exception as e:
        logger.exception("cp error")
        await reply_message(event.message, f"❌ Error: {str(e)}")


# ===================================================================
# COMMAND HANDLERS - COMPRESSION
# ===================================================================

@client.on(events.NewMessage(pattern=r'/zip\s+(.+)', func=lambda e: e.is_private))
async def handle_zip(event):
    """Handle /zip command."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado.")
        return
    
    user_id = event.sender_id
    user_root = get_user_root_path(user_id)
    current = CURRENT_DIRS.get(user_id, user_root)
    
    source_name = event.pattern_match.group(1).strip()
    
    async with ZIP_SEMAPHORE:
        try:
            current = Path(current).resolve()
            user_root = user_root.resolve()
            
            source = (current / source_name).resolve()
            
            # Security check
            if not str(source).startswith(str(user_root)):
                await reply_message(event.message, "❌ Acceso denegado.")
                return
            
            if not source.exists():
                await reply_message(event.message, "❌ No existe.")
                return
            
            progress_msg = await reply_message(event.message, "⏳ Iniciando compresión...")
            
            archive_name = f"{source.name}.zip"
            archive_path = current / archive_name
            
            start_time = time.time()
            
            def compress_sync():
                """Synchronous compression."""
                with zipfile.ZipFile(archive_path, 'w', zipfile.ZIP_DEFLATED) as zf:
                    if source.is_dir():
                        for root, dirs, files in os.walk(source):
                            for file in files:
                                file_path = Path(root) / file
                                arcname = file_path.relative_to(source.parent)
                                zf.write(file_path, arcname)
                    else:
                        zf.write(source, source.name)
            
            await asyncio.wait_for(
                asyncio.to_thread(compress_sync),
                timeout=FALLBACK_ZIP_TIMEOUT
            )
            
            elapsed = time.time() - start_time
            size = archive_path.stat().st_size
            
            text = f"✅ Archivo comprimido:\n<code>{archive_path.name}</code>\n\nTamaño: <b>{human_size(size)}</b>\nTiempo: <b>{_format_duration(elapsed)}</b>"
            await edit_message(progress_msg, text)
            
        except asyncio.TimeoutError:
            await edit_message(progress_msg, "❌ Timeout en compresión.")
        except Exception as e:
            logger.exception("zip error")
            await edit_message(progress_msg, f"❌ Error: {str(e)}")


@client.on(events.NewMessage(pattern=r'/unzip\s+(.+)', func=lambda e: e.is_private))
async def handle_unzip(event):
    """Handle /unzip command."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado.")
        return
    
    user_id = event.sender_id
    user_root = get_user_root_path(user_id)
    current = CURRENT_DIRS.get(user_id, user_root)
    
    archive_name = event.pattern_match.group(1).strip()
    
    async with ZIP_SEMAPHORE:
        try:
            current = Path(current).resolve()
            user_root = user_root.resolve()
            
            archive_path = (current / archive_name).resolve()
            
            # Security check
            if not str(archive_path).startswith(str(user_root)):
                await reply_message(event.message, "❌ Acceso denegado.")
                return
            
            if not archive_path.exists() or not archive_path.is_file():
                await reply_message(event.message, "❌ Archivo no existe.")
                return
            
            progress_msg = await reply_message(event.message, "⏳ Iniciando descompresión...")
            
            # Intentar usar 'unar' si está disponible
            use_unar = False
            try:
                result = await asyncio.wait_for(
                    asyncio.to_thread(subprocess.run, ['which', 'unar'], capture_output=True),
                    timeout=2
                )
                use_unar = result.returncode == 0
            except Exception:
                pass
            
            start_time = time.time()
            
            if use_unar:
                # Usar unar para descompresión
                try:
                    cmd = ['unar', '-o', str(current), str(archive_path)]
                    proc = await asyncio.wait_for(
                        asyncio.to_thread(subprocess.run, cmd, capture_output=True, text=True),
                        timeout=FALLBACK_ZIP_TIMEOUT
                    )
                    if proc.returncode != 0:
                        raise RuntimeError(proc.stderr)
                except Exception as e:
                    logger.warning(f"unar failed: {e}, falling back to zipfile")
                    use_unar = False
            
            if not use_unar:
                # Usar zipfile como fallback
                def extract_sync():
                    with zipfile.ZipFile(archive_path, 'r') as zf:
                        zf.extractall(current)
                
                await asyncio.wait_for(
                    asyncio.to_thread(extract_sync),
                    timeout=FALLBACK_ZIP_TIMEOUT
                )
            
            elapsed = time.time() - start_time
            
            text = f"✅ Archivo descomprimido\nTiempo: <b>{_format_duration(elapsed)}</b>"
            await edit_message(progress_msg, text)
            
        except asyncio.TimeoutError:
            await edit_message(progress_msg, "❌ Timeout en descompresión.")
        except Exception as e:
            logger.exception("unzip error")
            await edit_message(progress_msg, f"❌ Error: {str(e)}")


# ===================================================================
# COMMAND HANDLERS - AUTOMATOR
# ===================================================================

@client.on(events.NewMessage(pattern='/automator_on', func=lambda e: e.is_private))
async def handle_automator_on(event):
    """Handle /automator_on command."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado.")
        return
    
    user_id = event.sender_id
    await set_automator_enabled(user_id, True)
    await reply_message(event.message, "✅ Automator <b>activado</b> para este usuario.\n\nLos archivos se comprimirán y subirán automáticamente.")


@client.on(events.NewMessage(pattern='/automator_off', func=lambda e: e.is_private))
async def handle_automator_off(event):
    """Handle /automator_off command."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado.")
        return
    
    user_id = event.sender_id
    await set_automator_enabled(user_id, False)
    await reply_message(event.message, "✅ Automator <b>desactivado</b> para este usuario.")


@client.on(events.NewMessage(pattern='/automator_status', func=lambda e: e.is_private))
async def handle_automator_status(event):
    """Handle /automator_status command."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado.")
        return
    
    user_id = event.sender_id
    enabled = await get_automator_enabled(user_id)
    status = "🟢 ACTIVADO" if enabled else "🔴 DESACTIVADO"
    
    text = f"<b>Estado del Automator:</b>\n\n{status}\n\nUsa /automator_on o /automator_off para cambiar."
    await reply_message(event.message, text)


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
# DOWNLOAD HANDLER
# ===================================================================

@client.on(events.NewMessage(func=lambda e: e.is_private and (
    e.text.startswith('http://') or e.text.startswith('https://') or 
    e.text.startswith('magnet:') or e.text.endswith('.torrent'))))
async def handle_download(event):
    """Handle download requests."""
    if not is_owner(event.sender_id):
        await reply_message(event.message, "Acceso denegado.")
        return
    
    link = event.text.strip()
    user_id = event.sender_id
    user_root = get_user_root_path(user_id)
    current = CURRENT_DIRS.get(user_id, user_root)
    
    try:
        current = Path(current).resolve()
        user_root = user_root.resolve()
        
        # Create user root if doesn't exist
        user_root.mkdir(parents=True, exist_ok=True)
        
        # Check disk quota
        ok, msg = await check_user_quota(user_id)
        if not ok:
            await reply_message(event.message, msg)
            return
        
        progress_msg = await reply_message(event.message, "⏳ Procesando descarga...")
        
        jd = None
        try:
            jd = await asyncio.wait_for(
                asyncio.to_thread(connect_jd),
                timeout=JD_API_TIMEOUT
            )
            
            device = await asyncio.wait_for(
                asyncio.to_thread(get_device_direct, jd, JD_DEVICE_NAME),
                timeout=JD_API_TIMEOUT
            )
            
            # Add download
            if is_magnet(link):
                logger.info(f"Adding magnet: {link[:50]}...")
                result = await asyncio.wait_for(
                    asyncio.to_thread(device.downloads_add, link),
                    timeout=JD_API_TIMEOUT
                )
            elif is_torrent_url(link):
                logger.info(f"Downloading torrent from: {link[:50]}...")
                # Download .torrent file
                async with aiohttp.ClientSession() as session:
                    async with session.get(link, timeout=aiohttp.ClientTimeout(total=30)) as resp:
                        if resp.status == 200:
                            torrent_data = await resp.read()
                            result = await asyncio.wait_for(
                                asyncio.to_thread(device.downloads_add, torrent_data),
                                timeout=JD_API_TIMEOUT
                            )
                        else:
                            raise RuntimeError(f"Failed to download torrent: {resp.status}")
            else:
                # Regular HTTP download
                logger.info(f"Adding HTTP download: {link[:50]}...")
                result = await asyncio.wait_for(
                    asyncio.to_thread(device.downloads_add, link),
                    timeout=JD_API_TIMEOUT
                )
            
            await edit_message(progress_msg, "✅ Descarga añadida a la cola de JDownloader.\n\nSe procesará automáticamente.")
            
        except Exception as e:
            logger.exception(f"Download error: {e}")
            await edit_message(progress_msg, f"❌ Error en descarga: {str(e)}")
        finally:
            if jd:
                try:
                    await asyncio.wait_for(
                        asyncio.to_thread(jd.disconnect),
                        timeout=JD_API_TIMEOUT
                    )
                except Exception:
                    pass
                    
    except Exception as e:
        logger.exception("handle_download error")
        await reply_message(event.message, f"❌ Error: {str(e)}")


# ===================================================================
# GRACEFUL SHUTDOWN
# ===================================================================

async def graceful_shutdown(signum=None, frame=None):
    """Graceful shutdown handler."""
    logger.info("Received shutdown signal, cleaning up...")
    
    # Save state
    try:
        save_persistent_state()
        logger.info("Persistent state saved")
    except Exception as e:
        logger.exception(f"Failed to save state: {e}")
    
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

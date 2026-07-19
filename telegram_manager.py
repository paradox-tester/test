#!/usr/bin/env python3
"""
Telegram Manager: Fault-tolerant state machine for bot operations.
Handles connection freezes, operation recovery, and persistent task state.
"""

import asyncio
import json
import logging
import time
from dataclasses import dataclass, asdict, field
from datetime import datetime, timezone
from enum import Enum
from pathlib import Path
from typing import Optional, Any, Dict, List, Tuple

try:
    import aiohttp
except ImportError:
    aiohttp = None

from pyrogram import Client
from pyrogram.errors import FloodWait

log = logging.getLogger("TelegramManager")

# ============================================================
# LEGACY CLASS - Maintained for backward compatibility
# ============================================================

class TelegramManager:
    """Legacy manager kept for backward compatibility."""
    def __init__(self, create_client_callback):
        self._create_client = create_client_callback
        self._client = None
        self._lock = asyncio.Lock()
        self._generation = 0

    @property
    def client(self):
        return self._client

    @property
    def generation(self):
        return self._generation

    async def start(self):
        async with self._lock:
            if self._client is not None:
                return

            self._client = await self._create_client()
            self._generation += 1

            log.info(
                "Telegram client started (generation %d)",
                self._generation,
            )

    async def restart(self):
        async with self._lock:

            old = self._client

            self._client = None

            if old is not None:
                try:
                    await old.stop()
                except Exception:
                    log.exception("Error stopping telegram client")

            self._client = await self._create_client()

            self._generation += 1

            log.warning(
                "Telegram client restarted (generation %d)",
                self._generation,
            )

    async def stop(self):
        async with self._lock:

            if self._client is None:
                return

            try:
                await self._client.stop()
            finally:
                self._client = None

    async def get(self):
        if self._client is None:
            await self.start()

        return self._client


# ============================================================
# STATE MANAGEMENT - NEW SYSTEM
# ============================================================

class OperationState(str, Enum):
    """Estados posibles de una operación."""
    PENDING = "pending"           # Esperando iniciar
    DOWNLOADING = "downloading"   # Descargando/monitoreando
    COMPRESSING = "compressing"   # Comprimiendo
    UPLOADING = "uploading"       # Subiendo
    FINALIZING = "finalizing"     # Limpieza final
    COMPLETED = "completed"       # Completado exitosamente
    FAILED = "failed"             # Falló
    FROZEN = "frozen"             # Se detectó congelamiento


@dataclass
class TaskState:
    """Estado persistente de una tarea."""
    task_id: str
    operation: str  # "download", "compress", "upload", "auto_process"
    state: OperationState = OperationState.PENDING
    
    # Información de progreso
    current_step: int = 0
    total_steps: int = 0
    current_bytes: int = 0
    total_bytes: int = 0
    
    # Metadatos
    user_id: int = 0
    chat_id: int = 0
    source_path: str = ""
    dest_path: str = ""
    
    # Timestamps
    created_at: float = field(default_factory=time.time)
    updated_at: float = field(default_factory=time.time)
    started_at: Optional[float] = None
    frozen_at: Optional[float] = None
    
    # Información de reconexión
    last_heartbeat: Optional[float] = None
    reconnect_attempts: int = 0
    max_reconnect_attempts: int = 5
    
    # Datos dinámicos (serializable)
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    # No serializable - solo en memoria
    _client: Optional[Client] = field(default=None, repr=False)
    _cancel_event: Optional[asyncio.Event] = field(default=None, repr=False)
    
    def to_dict(self) -> dict:
        """Convierte a diccionario serializable."""
        data = asdict(self)
        data.pop("_client", None)
        data.pop("_cancel_event", None)
        data["state"] = self.state.value
        return data
    
    @classmethod
    def from_dict(cls, data: dict) -> "TaskState":
        """Reconstruye desde diccionario."""
        data_copy = data.copy()
        data_copy.pop("_client", None)
        data_copy.pop("_cancel_event", None)
        
        if isinstance(data_copy.get("state"), str):
            data_copy["state"] = OperationState(data_copy["state"])
        
        return cls(**data_copy)
    
    def is_stale(self, timeout_seconds: float = 300) -> bool:
        """Detecta si la tarea se congeló (sin heartbeat)."""
        if self.last_heartbeat is None:
            return False
        return (time.time() - self.last_heartbeat) > timeout_seconds
    
    def mark_frozen(self):
        """Marca la tarea como congelada."""
        self.state = OperationState.FROZEN
        self.frozen_at = time.time()
    
    def update_heartbeat(self):
        """Actualiza timestamp de latido."""
        self.last_heartbeat = time.time()
        self.updated_at = time.time()


# ============================================================
# STATE PERSISTENCE
# ============================================================

class StateManager:
    """Gestiona persistencia de estado de tareas."""
    
    def __init__(self, state_dir: Path = None):
        self.state_dir = state_dir or (Path.cwd() / "task_states")
        self.state_dir.mkdir(exist_ok=True)
        self._lock = asyncio.Lock()
        self._states: Dict[str, TaskState] = {}
        self._load_all()
        log.info(f"StateManager initialized at {self.state_dir}")
    
    def _load_all(self):
        """Carga todos los estados persitidos."""
        try:
            for state_file in self.state_dir.glob("*.json"):
                try:
                    with open(state_file, "r") as f:
                        data = json.load(f)
                        task = TaskState.from_dict(data)
                        self._states[task.task_id] = task
                        log.info(f"Loaded state for task {task.task_id}: {task.state.value}")
                except Exception as e:
                    log.warning(f"Failed to load {state_file}: {e}")
        except Exception as e:
            log.error(f"Error loading states: {e}")
    
    async def save(self, task: TaskState):
        """Guarda estado de tarea de forma thread-safe."""
        async with self._lock:
            self._states[task.task_id] = task
            state_file = self.state_dir / f"{task.task_id}.json"
            try:
                with open(state_file, "w") as f:
                    json.dump(task.to_dict(), f, indent=2)
            except Exception as e:
                log.error(f"Failed to save state for {task.task_id}: {e}")
    
    async def load(self, task_id: str) -> Optional[TaskState]:
        """Carga estado de tarea."""
        async with self._lock:
            return self._states.get(task_id)
    
    async def get_stale_tasks(self, timeout_seconds: float = 300) -> List[TaskState]:
        """Obtiene tareas congeladas."""
        async with self._lock:
            return [t for t in self._states.values() if t.is_stale(timeout_seconds)]
    
    async def delete(self, task_id: str):
        """Elimina estado de tarea."""
        async with self._lock:
            self._states.pop(task_id, None)
            state_file = self.state_dir / f"{task_id}.json"
            try:
                state_file.unlink(missing_ok=True)
            except Exception as e:
                log.warning(f"Failed to delete state file {state_file}: {e}")
    
    async def get_all_active(self) -> List[TaskState]:
        """Obtiene todas las tareas activas."""
        async with self._lock:
            return [t for t in self._states.values() 
                   if t.state not in (OperationState.COMPLETED, OperationState.FAILED)]


# ============================================================
# RESILIENT CLIENT WRAPPER
# ============================================================

class ResilientClient:
    """Wrapper alrededor del cliente Pyrogram con recuperación automática."""
    
    def __init__(self, client: Client, state_manager: StateManager, 
                 freeze_timeout: float = 90, reconnect_timeout: float = 15):
        self.client = client
        self.state_manager = state_manager
        self.freeze_timeout = freeze_timeout
        self.reconnect_timeout = reconnect_timeout
        self._last_activity = time.time()
        self._lock = asyncio.Lock()
        self._frozen = False
    
    async def _check_and_recover(self) -> bool:
        """Verifica congelamiento e intenta recuperación."""
        now = time.time()
        if now - self._last_activity > self.freeze_timeout and not self._frozen:
            log.critical("CLIENT FREEZE DETECTED - attempting recovery")
            self._frozen = True
            return await self._recover()
        return True
    
    async def _recover(self) -> bool:
        """Intenta recuperar cliente congelado."""
        async with self._lock:
            try:
                # 1. Obtener tareas congeladas
                stale_tasks = await self.state_manager.get_stale_tasks(self.freeze_timeout)
                for task in stale_tasks:
                    task.mark_frozen()
                    task.reconnect_attempts += 1
                    await self.state_manager.save(task)
                    log.warning(f"Marked task {task.task_id} as frozen (attempt {task.reconnect_attempts})")
                
                # 2. Intentar reconectar
                log.info("Attempting client reconnection...")
                if not self.client.is_connected:
                    await asyncio.wait_for(self.client.reconnect(), timeout=self.reconnect_timeout)
                    log.info("Client reconnected successfully")
                
                # 3. Intentar operación simple de prueba
                await asyncio.wait_for(self.client.get_me(), timeout=10.0)
                log.info("Client health check passed")
                
                self._frozen = False
                self._last_activity = time.time()
                return True
                
            except asyncio.TimeoutError:
                log.error("Reconnection timeout - client may be unreachable")
                return False
            except Exception as e:
                log.error(f"Recovery failed: {e}")
                return False
    
    async def edit_message_resilient(self, message, text: str, **kwargs) -> bool:
        """Edita mensaje con recuperación automática."""
        await self._check_and_recover()
        
        for attempt in range(3):
            try:
                await asyncio.wait_for(
                    message.edit(text, **kwargs),
                    timeout=20.0
                )
                self._last_activity = time.time()
                return True
            except FloodWait as e:
                log.warning(f"FloodWait: waiting {e.value}s")
                await asyncio.sleep(e.value)
            except asyncio.TimeoutError:
                log.warning(f"Edit timeout (attempt {attempt + 1})")
                if attempt == 2:
                    return False
                await asyncio.sleep(2 ** attempt)
            except Exception as e:
                log.error(f"Edit failed: {e}")
                return False
        
        return False
    
    async def send_document_resilient(self, chat_id: int, file_path: str, 
                                     caption: str = "", progress=None, **kwargs) -> Optional[Any]:
        """Envía documento con recuperación automática."""
        await self._check_and_recover()
        
        for attempt in range(5):
            try:
                result = await asyncio.wait_for(
                    self.client.send_document(
                        chat_id=chat_id,
                        document=file_path,
                        caption=caption,
                        progress=progress,
                        **kwargs
                    ),
                    timeout=3600.0  # 1 hora para uploads grandes
                )
                self._last_activity = time.time()
                return result
            except FloodWait as e:
                log.warning(f"FloodWait in upload: {e.value}s")
                await asyncio.sleep(e.value)
            except asyncio.TimeoutError as e:
                log.warning(f"Send attempt {attempt + 1} failed: timeout")
                if attempt < 4:
                    await asyncio.sleep(5 * (2 ** attempt))
            except Exception as e:
                log.error(f"Send failed: {e}")
                raise
        
        return None
    
    def update_heartbeat(self, task_id: str):
        """Actualiza latido de tarea."""
        self._last_activity = time.time()


# ============================================================
# OPERATION TRACKER
# ============================================================

class OperationTracker:
    """Monitorea operaciones y detecta congelamientos."""
    
    def __init__(self, state_manager: StateManager, check_interval: float = 10):
        self.state_manager = state_manager
        self.check_interval = check_interval
        self._monitoring = False
    
    async def start_monitoring(self):
        """Inicia monitoreo de operaciones congeladas."""
        if self._monitoring:
            return
        self._monitoring = True
        asyncio.create_task(self._monitor_loop())
        log.info("Operation monitoring started")
    
    async def _monitor_loop(self):
        """Loop de monitoreo."""
        while self._monitoring:
            try:
                await asyncio.sleep(self.check_interval)
                stale_tasks = await self.state_manager.get_stale_tasks()
                
                for task in stale_tasks:
                    log.warning(f"⚠️ Stale task detected: {task.task_id}")
                    log.warning(f"   Operation: {task.operation}")
                    log.warning(f"   State: {task.state.value}")
                    log.warning(f"   No activity for {time.time() - task.last_heartbeat:.0f}s")
                    
                    if task.reconnect_attempts < task.max_reconnect_attempts:
                        log.info(f"   → Will attempt recovery ({task.reconnect_attempts}/{task.max_reconnect_attempts})")
                    else:
                        log.error(f"   → Max reconnection attempts exceeded - marking as failed")
                        task.state = OperationState.FAILED
                        await self.state_manager.save(task)
                        
            except Exception as e:
                log.error(f"Error in monitor loop: {e}")
    
    async def stop_monitoring(self):
        """Detiene monitoreo."""
        self._monitoring = False


# ============================================================
# HELPER: Operation Context Manager
# ============================================================

class OperationContext:
    """Context manager para operaciones con estado automático."""
    
    def __init__(self, task: TaskState, state_manager: StateManager, 
                 client_wrapper: ResilientClient):
        self.task = task
        self.state_manager = state_manager
        self.client_wrapper = client_wrapper
    
    async def __aenter__(self):
        self.task.started_at = time.time()
        self.task.state = OperationState.PENDING
        await self.state_manager.save(self.task)
        log.info(f"Operation started: {self.task.task_id}")
        return self
    
    async def __aexit__(self, exc_type, exc_val, exc_tb):
        if exc_type is not None:
            self.task.state = OperationState.FAILED
            log.error(f"Operation failed: {exc_val}")
        else:
            self.task.state = OperationState.COMPLETED
            log.info(f"Operation completed: {self.task.task_id}")
        
        await self.state_manager.save(self.task)
        
        # Limpiar después de completarse
        await asyncio.sleep(1)
        await self.state_manager.delete(self.task.task_id)
    
    async def update_progress(self, step: int, current_bytes: int = None, 
                            state: OperationState = None):
        """Actualiza progreso de operación."""
        self.task.current_step = step
        if current_bytes is not None:
            self.task.current_bytes = current_bytes
        if state is not None:
            self.task.state = state
        
        self.task.update_heartbeat()
        await self.state_manager.save(self.task)
        self.client_wrapper.update_heartbeat(self.task.task_id)


# ============================================================
# INITIALIZATION HELPER
# ============================================================

async def initialize_fault_tolerance(client: Client, 
                                     state_dir: Optional[Path] = None) -> Tuple[StateManager, ResilientClient, OperationTracker]:
    """Inicializa sistema de tolerancia a fallos."""
    
    state_manager = StateManager(state_dir)
    client_wrapper = ResilientClient(client, state_manager)
    tracker = OperationTracker(state_manager)
    
    await tracker.start_monitoring()
    
    log.info("Fault tolerance system initialized")
    return state_manager, client_wrapper, tracker

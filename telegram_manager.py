import asyncio
import logging
from typing import Optional

log = logging.getLogger("TelegramManager")


class TelegramManager:
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
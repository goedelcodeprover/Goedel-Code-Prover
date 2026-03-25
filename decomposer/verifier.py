"""Decomposer Lean verifier — thin wrapper over common.lean_client.

Adds threading.Semaphore-based concurrency control on top of the
unified sync verification functions.
"""
from __future__ import annotations

import logging
import threading
from typing import Any

from common.lean_client import (
    close_sync_session,
    verify_lean_code as _verify,
    verify_lean_code_batch as _verify_batch,
    HTTP_POOL_MIN_SIZE,
)

logger = logging.getLogger(__name__)


# ---- Semaphore for decomposer concurrency limit ----

_lean_semaphore: threading.Semaphore | None = None
_semaphore_lock = threading.Lock()


def _get_lean_semaphore() -> threading.Semaphore:
    global _lean_semaphore
    if _lean_semaphore is not None:
        return _lean_semaphore
    with _semaphore_lock:
        if _lean_semaphore is not None:
            return _lean_semaphore
        from .utils import get_config
        cfg = get_config()
        max_concurrent = getattr(cfg, "lean_max_concurrent", 48)
        _lean_semaphore = threading.Semaphore(max_concurrent)
        logger.info("Lean semaphore initialized: max_concurrent=%d", max_concurrent)
        return _lean_semaphore


def _pool_maxsize() -> int:
    from .utils import get_config
    cfg = get_config()
    return max(getattr(cfg, "lean_max_concurrent", HTTP_POOL_MIN_SIZE), HTTP_POOL_MIN_SIZE)


# ---- Public API (same signatures as before) ----

def close_http_session() -> None:
    """Close the global HTTP session"""
    close_sync_session()


def verify_lean_code(
    lean_code: str,
    server_url: str = "http://localhost:8000",
    timeout: int = 60,
) -> dict[str, Any]:
    """Verify Lean code (semaphore rate limiting + retry)"""
    with _get_lean_semaphore():
        return _verify(
            lean_code, server_url, timeout,
            pool_maxsize=_pool_maxsize(),
        )


def verify_lean_code_batch(
    codes: list[str],
    server_url: str = "http://localhost:8000",
    timeout: int = 60,
) -> list[dict[str, Any]]:
    """Batch verify Lean code (semaphore rate limiting + retry)"""
    with _get_lean_semaphore():
        return _verify_batch(
            codes, server_url, timeout,
            pool_maxsize=_pool_maxsize(),
        )


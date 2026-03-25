"""Unified Lean verification server client.

Provides sync (requests) and async (aiohttp) verification interfaces
shared by decomposer and prover.
"""
from __future__ import annotations

import asyncio
import logging
import threading
import time
from typing import Any, Callable, Dict, List, Tuple

import aiohttp
import requests
from requests.adapters import HTTPAdapter

logger = logging.getLogger(__name__)

MAX_RETRIES = 5
INITIAL_RETRY_DELAY = 1.0
RETRY_BACKOFF_MULTIPLIER = 2
TIMEOUT_BUFFER_DEFAULT = 60
LEAN_OVERFLOW_THRESHOLD = 2
LEAN_MAX_RETRIES = 1
HTTP_POOL_MIN_SIZE = 256
HTTP_POOL_CONNECTIONS = 64
AIOHTTP_POOL_SIZE = 300
AIOHTTP_CONNECT_TIMEOUT = 15
ASYNC_RETRY_BACKOFF_BASE = 0.5


# ---- Sync HTTP session ----

_sync_session: requests.Session | None = None
_sync_session_lock = threading.Lock()


def _get_sync_session(pool_maxsize: int = HTTP_POOL_MIN_SIZE) -> requests.Session:
    global _sync_session
    if _sync_session is not None:
        return _sync_session
    with _sync_session_lock:
        if _sync_session is not None:
            return _sync_session
        session = requests.Session()
        adapter = HTTPAdapter(
            pool_connections=HTTP_POOL_CONNECTIONS,
            pool_maxsize=max(pool_maxsize, HTTP_POOL_MIN_SIZE),
            max_retries=0,
        )
        session.mount("http://", adapter)
        session.mount("https://", adapter)
        _sync_session = session
        logger.info("Sync HTTP session initialized (pool_maxsize=%d)", pool_maxsize)
        return _sync_session


def close_sync_session() -> None:
    global _sync_session
    with _sync_session_lock:
        if _sync_session is not None:
            _sync_session.close()
            _sync_session = None


# ---- Async HTTP session ----

_async_session: aiohttp.ClientSession | None = None
_async_session_lock: asyncio.Lock | None = None


def _get_async_lock() -> asyncio.Lock:
    global _async_session_lock
    if _async_session_lock is None:
        _async_session_lock = asyncio.Lock()
    return _async_session_lock


async def _get_async_session() -> aiohttp.ClientSession:
    global _async_session
    if _async_session is not None and not _async_session.closed:
        return _async_session
    lock = _get_async_lock()
    async with lock:
        if _async_session is not None and not _async_session.closed:
            return _async_session
        connector = aiohttp.TCPConnector(
            limit=AIOHTTP_POOL_SIZE,
            limit_per_host=AIOHTTP_POOL_SIZE,
            force_close=True,
        )
        timeout = aiohttp.ClientTimeout(sock_connect=AIOHTTP_CONNECT_TIMEOUT)
        _async_session = aiohttp.ClientSession(connector=connector, timeout=timeout)
        return _async_session


async def close_async_session() -> None:
    global _async_session
    if _async_session is not None and not _async_session.closed:
        await _async_session.close()
        _async_session = None


# ---- Payload ----

def _build_verify_payload(code: str, timeout: int) -> dict:
    return {
        "code": code,
        "timeout": timeout,
        "max_retries": LEAN_MAX_RETRIES,
        "overflow_threshold": LEAN_OVERFLOW_THRESHOLD,
    }


# ---- Sync verification ----

def _retry_delay(attempt: int) -> float:
    return INITIAL_RETRY_DELAY * (RETRY_BACKOFF_MULTIPLIER ** attempt)


def _is_retryable(e: Exception) -> bool:
    if isinstance(e, (requests.Timeout, requests.ConnectionError)):
        return True
    if isinstance(e, requests.RequestException) and hasattr(e.response, "status_code"):
        return 500 <= e.response.status_code < 600
    return False


def _sync_post_with_retry(
    url: str,
    payload: dict,
    timeout: float,
    context: str = "Lean request",
    result_extractor: Callable[[dict], Any] | None = None,
    pool_maxsize: int = HTTP_POOL_MIN_SIZE,
) -> Any:
    last_exc: Exception | None = None
    session = _get_sync_session(pool_maxsize)
    for attempt in range(MAX_RETRIES):
        try:
            resp = session.post(url, json=payload, timeout=timeout)
            resp.raise_for_status()
            result = resp.json()
            if attempt > 0:
                logger.info("%s: succeeded after %d attempts", context, attempt + 1)
            return result_extractor(result) if result_extractor else result
        except requests.Timeout as e:
            last_exc = e
            if attempt < MAX_RETRIES - 1:
                d = _retry_delay(attempt)
                logger.warning("%s: timeout (attempt %d/%d), retry in %.1fs", context, attempt + 1, MAX_RETRIES, d)
                time.sleep(d)
            else:
                raise RuntimeError(f"{context}: timed out after {MAX_RETRIES} retries") from None
        except requests.RequestException as e:
            last_exc = e
            if _is_retryable(e) and attempt < MAX_RETRIES - 1:
                d = _retry_delay(attempt)
                logger.warning("%s: error (attempt %d/%d): %s, retry in %.1fs", context, attempt + 1, MAX_RETRIES, e, d)
                time.sleep(d)
            else:
                raise RuntimeError(f"{context}: request failed: {e}") from e
        except ValueError as e:
            raise ValueError(f"{context}: invalid response: {e}") from e
    if last_exc:
        raise RuntimeError(f"{context}: failed after {MAX_RETRIES} retries") from last_exc


def verify_lean_code(
    code: str,
    server_url: str,
    timeout: int = 60,
    timeout_buffer: int = TIMEOUT_BUFFER_DEFAULT,
    pool_maxsize: int = HTTP_POOL_MIN_SIZE,
) -> dict[str, Any]:
    """Sync Lean code verification with retry."""
    url = f"{server_url.rstrip(chr(47))}/verify"
    payload = _build_verify_payload(code, timeout)
    return _sync_post_with_retry(
        url=url, payload=payload,
        timeout=timeout + timeout_buffer,
        context="Lean verify",
        pool_maxsize=pool_maxsize,
    )


def verify_lean_code_batch(
    codes: list[str],
    server_url: str,
    timeout: int = 60,
    timeout_buffer: int = TIMEOUT_BUFFER_DEFAULT,
    pool_maxsize: int = HTTP_POOL_MIN_SIZE,
) -> list[dict[str, Any]]:
    """Sync batch Lean code verification."""
    url = f"{server_url.rstrip(chr(47))}/verify/batch"
    batch_timeout = max(len(codes) * timeout + timeout_buffer, timeout * 2)
    payload = {
        "codes": codes,
        "timeout": timeout,
        "max_retries": LEAN_MAX_RETRIES,
        "overflow_threshold": LEAN_OVERFLOW_THRESHOLD,
    }
    return _sync_post_with_retry(
        url=url, payload=payload,
        timeout=batch_timeout,
        context=f"Lean batch verify (n={len(codes)})",
        result_extractor=lambda r: r.get("results", []),
        pool_maxsize=pool_maxsize,
    )


# ---- Async verification ----

async def verify_lean_code_async(
    code: str,
    server_url: str,
    timeout: int = 60,
    timeout_buffer: int = TIMEOUT_BUFFER_DEFAULT,
) -> dict[str, Any]:
    """Async Lean code verification (retries on connection errors only)."""
    url = f"{server_url.rstrip(chr(47))}/verify"
    payload = _build_verify_payload(code, timeout)
    http_timeout = aiohttp.ClientTimeout(total=timeout + timeout_buffer)
    last_error: Exception | None = None
    for attempt in range(MAX_RETRIES):
        try:
            session = await _get_async_session()
            async with session.post(url, json=payload, timeout=http_timeout) as resp:
                resp.raise_for_status()
                return await resp.json()
        except asyncio.TimeoutError:
            logger.warning("[Lean Verify Async] timeout (%ds)", timeout)
            return {"error": "timeout", "is_valid": False}
        except (aiohttp.ServerDisconnectedError, aiohttp.ClientOSError,
                aiohttp.ClientConnectionError, ConnectionResetError) as e:
            last_error = e
            delay = ASYNC_RETRY_BACKOFF_BASE * (2 ** attempt)
            if attempt < MAX_RETRIES - 1:
                logger.warning("[Lean Verify Async] connection error (%d/%d): %s, retry in %.1fs", attempt + 1, MAX_RETRIES, e, delay)
                await asyncio.sleep(delay)
            else:
                logger.error("[Lean Verify Async] connection error after %d attempts: %s", MAX_RETRIES, e)
        except aiohttp.ClientError as e:
            logger.error("[Lean Verify Async] request failed: %s", e)
            return {"error": str(e), "is_valid": False}
    return {"error": str(last_error), "is_valid": False}


# ---- Result parsing ----

def check_verification_result(result: Dict) -> Tuple[bool, bool, List[str]]:
    """Parse verification result -> (no_sorry, with_sorry, errors)."""
    if "error" in result:
        return False, False, [result.get("error", "Unknown error")]
    is_valid_no_sorry = result.get("is_valid_no_sorry", False)
    is_valid_with_sorry = result.get("is_valid_with_sorry", False)
    ok, errors = result.get("error_message", (False, []))
    error_list = errors if isinstance(errors, list) else [str(errors)] if errors else []
    return is_valid_no_sorry, is_valid_with_sorry, error_list


def extract_unsolved_goals(result: Dict) -> List[Dict]:
    """Extract unsolved goals (sorry targets) from verification result."""
    unsolved_goals: List[Dict] = []
    try:
        inner = result.get("response") or {}
        inner = inner.get("response") or {}
        sorries = inner.get("sorries") or []
        for sorry_info in sorries:
            line_num = sorry_info.get("pos", {}).get("line", 0)
            goal = sorry_info.get("goal", "")
            if goal:
                turnstile = chr(8866)
                if turnstile in goal:
                    goal_type = goal.split(turnstile, 1)[-1].strip()
                else:
                    goal_type = goal.strip()
                unsolved_goals.append({
                    "line": line_num,
                    "goal": turnstile + " " + goal_type,
                    "full_goal": goal,
                })
            else:
                unsolved_goals.append({
                    "line": line_num,
                    "goal": "sorry (no goal info)",
                    "full_goal": "",
                })
    except Exception as e:
        logger.warning("Failed to extract unsolved goals: %s", e)
    return unsolved_goals


def get_sorry_context(code: str, line_num: int, context_lines: int = 5) -> str:
    """Get code context around a sorry location."""
    lines = code.split(chr(10))
    start = max(0, line_num - context_lines - 1)
    end = min(len(lines), line_num + context_lines)
    ctx = []
    for i in range(start, end):
        prefix = ">>> " if i == line_num - 1 else "    "
        ctx.append(f"{prefix}{i + 1:4d} | {lines[i]}")
    return chr(10).join(ctx)

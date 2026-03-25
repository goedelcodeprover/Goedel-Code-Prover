"""Unified logging: per-problem logger creation and noisy logger suppression."""
from __future__ import annotations

import logging
from pathlib import Path

NOISY_LOGGERS = [
    'azure.identity', 'azure.core', 'azure.core.pipeline',
    'azure.core.pipeline.policies', 'urllib3', 'urllib3.connectionpool',
    'httpx', 'httpcore', 'openai',
]

LOG_FORMAT = '%(asctime)s - %(levelname)s - %(message)s'


def suppress_noisy_loggers() -> None:
    """Suppress noisy third-party library loggers to WARNING level."""
    for name in NOISY_LOGGERS:
        logging.getLogger(name).setLevel(logging.WARNING)


def setup_problem_logger(
    problem_id: str,
    log_dir: str,
    prefix: str = "",
    propagate: bool = True,
) -> logging.Logger:
    """Create a per-problem logger.

    Each call clears old handlers and recreates them to ensure logs are
    written to the correct file.

    Args:
        problem_id: Problem ID (may contain `/` or `\\`; automatically sanitized).
        log_dir: Directory path for log files.
        prefix: Logger name prefix (e.g. ``"decompose"`` or ``"prove"``).
        propagate: Whether to propagate to the root logger.
    """
    Path(log_dir).mkdir(parents=True, exist_ok=True)
    safe_id = safe_problem_id(problem_id)
    log_file = Path(log_dir) / f"{safe_id}.log"

    logger_name = f"{prefix}_{safe_id}" if prefix else safe_id
    plogger = logging.getLogger(logger_name)
    plogger.setLevel(logging.DEBUG)
    plogger.propagate = propagate

    for h in plogger.handlers[:]:
        h.close()
        plogger.removeHandler(h)

    fh = logging.FileHandler(log_file, encoding='utf-8')
    fh.setFormatter(logging.Formatter(LOG_FORMAT))
    plogger.addHandler(fh)

    return plogger


def cleanup_logger(plogger: logging.Logger) -> None:
    """Clean up all handlers on a logger, releasing file descriptors."""
    for handler in plogger.handlers[:]:
        handler.close()
        plogger.removeHandler(handler)


def safe_problem_id(problem_id: str) -> str:
    """Convert a problem_id to a safe filename segment."""
    return problem_id.replace("/", "_").replace("\\", "_")

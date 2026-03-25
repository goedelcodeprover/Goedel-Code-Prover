"""IO utilities: safe filenames, JSON result saving and loading."""
from __future__ import annotations

import json
import logging
from pathlib import Path
from typing import Any

logger = logging.getLogger(__name__)


def safe_filename(name: str, extension: str = ".json") -> str:
    """Convert an arbitrary string to a safe filename."""
    safe = name.replace("/", "_").replace("\\", "_").replace(" ", "_")
    if extension and not safe.endswith(extension):
        safe += extension
    return safe


def save_json(data: Any, directory: str | Path, name: str, extension: str = ".json") -> Path:
    """Serialize data to JSON and write it to *directory/safe(name)*.

    Returns:
        Path of the written file.
    """
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    filename = safe_filename(name, extension)
    filepath = directory / filename
    with open(filepath, 'w', encoding='utf-8') as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
    return filepath


def load_json(filepath: str | Path | None) -> dict | None:
    """Load JSON from disk; silently returns None on failure."""
    if filepath is None:
        return None
    filepath = Path(filepath)
    if not filepath.exists():
        return None
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            return json.load(f)
    except Exception:
        return None

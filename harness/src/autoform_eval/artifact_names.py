from __future__ import annotations

import hashlib
import re
from typing import Any


_SAFE_COMPONENT_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")
_UNSAFE_COMPONENT_CHARS_RE = re.compile(r"[^A-Za-z0-9._-]+")
_MAX_COMPONENT_LEN = 80


def artifact_component(value: Any, *, max_len: int = _MAX_COMPONENT_LEN) -> str:
    """Return a single safe filename component for a provenance value."""
    text = str(value).strip()
    if _SAFE_COMPONENT_RE.fullmatch(text) and len(text) <= max_len:
        return text

    digest = hashlib.sha256(text.encode("utf-8")).hexdigest()[:10]
    stem = _UNSAFE_COMPONENT_CHARS_RE.sub("_", text).strip("._-")
    if not stem:
        stem = "value"
    stem = stem[:max_len].strip("._-") or "value"
    return f"{stem}-{digest}"


def artifact_stem(*values: Any) -> str:
    return ".".join(artifact_component(value) for value in values)


__all__ = ["artifact_component", "artifact_stem"]

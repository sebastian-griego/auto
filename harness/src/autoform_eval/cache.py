from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


def stable_hash(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


class JsonCache:
    def __init__(self, root: Path):
        self.root = root

    def _path(self, namespace: str, key: str) -> Path:
        return self.root / namespace / f"{key}.json"

    def get(self, namespace: str, key: str) -> dict[str, Any] | None:
        path = self._path(namespace, key)
        if not path.exists():
            return None
        with path.open("r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            return data
        return None

    def set(self, namespace: str, key: str, value: dict[str, Any]) -> Path:
        path = self._path(namespace, key)
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("w", encoding="utf-8") as f:
            json.dump(value, f, indent=2, sort_keys=True)
            f.write("\n")
        return path

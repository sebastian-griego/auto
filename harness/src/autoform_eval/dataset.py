from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Iterable

from .types import DatasetItem, ProvenanceSpec, SemanticSpec


ALLOWED_TIER = {"A", "B"}
ALLOWED_SPLIT = {"pilot", "dev", "test"}
ALLOWED_KIND = {"normalized_ref", "decidable_ref", "behavioral"}
ALLOWED_SOURCE_KIND = {"mathlib_decl", "textbook", "competition", "other"}


class DatasetError(ValueError):
    pass


def _expect_str(d: dict[str, Any], key: str, where: str) -> str:
    v = d.get(key)
    if not isinstance(v, str) or not v:
        raise DatasetError(f"{where}: '{key}' must be a non-empty string")
    return v


def _expect_str_list(d: dict[str, Any], key: str, where: str) -> list[str]:
    v = d.get(key)
    if not isinstance(v, list) or not all(isinstance(x, str) for x in v):
        raise DatasetError(f"{where}: '{key}' must be a list[string]")
    return list(v)


def parse_item(raw: dict[str, Any], where: str) -> DatasetItem:
    semantic_raw = raw.get("semantic")
    provenance_raw = raw.get("provenance")
    if not isinstance(semantic_raw, dict):
        raise DatasetError(f"{where}: 'semantic' must be an object")
    if not isinstance(provenance_raw, dict):
        raise DatasetError(f"{where}: 'provenance' must be an object")

    split = _expect_str(raw, "split", where)
    tier = _expect_str(raw, "tier", where)
    kind = _expect_str(semantic_raw, "kind", f"{where}.semantic")
    source_kind = _expect_str(provenance_raw, "source_kind", f"{where}.provenance")

    if split not in ALLOWED_SPLIT:
        raise DatasetError(f"{where}: unsupported split '{split}'")
    if tier not in ALLOWED_TIER:
        raise DatasetError(f"{where}: unsupported tier '{tier}'")
    if kind not in ALLOWED_KIND:
        raise DatasetError(f"{where}: unsupported semantic.kind '{kind}'")
    if source_kind not in ALLOWED_SOURCE_KIND:
        raise DatasetError(f"{where}: unsupported provenance.source_kind '{source_kind}'")

    semantic = SemanticSpec(
        kind=kind,
        check=_expect_str(semantic_raw, "check", f"{where}.semantic"),
        extra=semantic_raw.get("extra") if isinstance(semantic_raw.get("extra"), str) else None,
    )
    provenance = ProvenanceSpec(
        source_kind=source_kind,
        source_ref=_expect_str(provenance_raw, "source_ref", f"{where}.provenance"),
        license=_expect_str(provenance_raw, "license", f"{where}.provenance"),
        notes=provenance_raw.get("notes") if isinstance(provenance_raw.get("notes"), str) else None,
    )

    forbidden_ok = raw.get("forbidden_ok", [])
    if forbidden_ok and (not isinstance(forbidden_ok, list) or not all(isinstance(x, str) for x in forbidden_ok)):
        raise DatasetError(f"{where}: 'forbidden_ok' must be list[string]")

    return DatasetItem(
        schema_version=_expect_str(raw, "schema_version", where),
        checker_version=_expect_str(raw, "checker_version", where),
        id=_expect_str(raw, "id", where),
        nl=_expect_str(raw, "nl", where),
        imports=_expect_str_list(raw, "imports", where),
        context=raw.get("context", "") if isinstance(raw.get("context", ""), str) else "",
        expected=_expect_str(raw, "expected", where),
        family=_expect_str(raw, "family", where),
        tier=tier,
        split=split,
        tags=_expect_str_list(raw, "tags", where),
        semantic=semantic,
        provenance=provenance,
        forbidden_ok=list(forbidden_ok),
    )


def load_jsonl(path: Path) -> list[DatasetItem]:
    if not path.exists():
        return []
    items: list[DatasetItem] = []
    with path.open("r", encoding="utf-8") as f:
        for idx, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                raw = json.loads(line)
            except json.JSONDecodeError as exc:
                raise DatasetError(f"{path}:{idx}: invalid JSON: {exc}") from exc
            if not isinstance(raw, dict):
                raise DatasetError(f"{path}:{idx}: each row must be a JSON object")
            items.append(parse_item(raw, f"{path}:{idx}"))
    return items


def split_path(dataset_dir: Path, split: str) -> Path:
    if split not in ALLOWED_SPLIT:
        raise DatasetError(f"unsupported split '{split}'")
    return dataset_dir / f"{split}.jsonl"


def load_split(dataset_dir: Path, split: str) -> list[DatasetItem]:
    return load_jsonl(split_path(dataset_dir, split))


def iter_all_splits(dataset_dir: Path) -> Iterable[tuple[str, list[DatasetItem]]]:
    for split in sorted(ALLOWED_SPLIT):
        yield split, load_split(dataset_dir, split)

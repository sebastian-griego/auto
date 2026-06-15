from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Iterable

from .types import DatasetItem, ProvenanceSpec, SemanticSpec


ALLOWED_TIER = {"A", "B"}
ALLOWED_SPLIT = {"pilot", "dev", "test"}
ALLOWED_KIND = {"normalized_ref", "decidable_ref", "behavioral"}
ALLOWED_SOURCE_KIND = {"mathlib_decl", "textbook", "competition", "assistant_generated", "other"}
CHECK_KEY_ALIASES = {
    "fin_truth_table_norm": "fin_truth_table",
}


class DatasetError(ValueError):
    pass


def _expect_str(d: dict[str, Any], key: str, where: str) -> str:
    v = d.get(key)
    if not isinstance(v, str) or not v:
        raise DatasetError(f"{where}: '{key}' must be a non-empty string")
    return v


def _expect_present_str(d: dict[str, Any], key: str, where: str) -> str:
    if key not in d:
        raise DatasetError(f"{where}: '{key}' must be a string")
    v = d[key]
    if not isinstance(v, str):
        raise DatasetError(f"{where}: '{key}' must be a string")
    return v


def _expect_str_list(d: dict[str, Any], key: str, where: str) -> list[str]:
    v = d.get(key)
    if not isinstance(v, list) or not all(isinstance(x, str) for x in v):
        raise DatasetError(f"{where}: '{key}' must be a list[string]")
    return list(v)


def _expect_optional_str(d: dict[str, Any], key: str, where: str) -> str | None:
    if key not in d or d[key] is None:
        return None
    v = d[key]
    if not isinstance(v, str):
        raise DatasetError(f"{where}: '{key}' must be a string when present")
    return v


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
    check = _expect_str(semantic_raw, "check", f"{where}.semantic")
    check = CHECK_KEY_ALIASES.get(check, check)
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
        check=check,
        extra=_expect_optional_str(semantic_raw, "extra", f"{where}.semantic"),
    )
    provenance = ProvenanceSpec(
        source_kind=source_kind,
        source_ref=_expect_str(provenance_raw, "source_ref", f"{where}.provenance"),
        license=_expect_str(provenance_raw, "license", f"{where}.provenance"),
        notes=_expect_optional_str(
            provenance_raw, "notes", f"{where}.provenance"
        ),
    )

    forbidden_ok = raw.get("forbidden_ok", [])
    if not isinstance(forbidden_ok, list) or not all(
        isinstance(x, str) for x in forbidden_ok
    ):
        raise DatasetError(f"{where}: 'forbidden_ok' must be list[string]")

    return DatasetItem(
        schema_version=_expect_str(raw, "schema_version", where),
        checker_version=_expect_str(raw, "checker_version", where),
        id=_expect_str(raw, "id", where),
        nl=_expect_str(raw, "nl", where),
        imports=_expect_str_list(raw, "imports", where),
        context=_expect_present_str(raw, "context", where),
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
    first_lines: dict[str, int] = {}
    with path.open("r", encoding="utf-8-sig") as f:
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
            item = parse_item(raw, f"{path}:{idx}")
            if item.id in first_lines:
                raise DatasetError(
                    f"duplicate id {item.id!r} at {path}:{idx}; "
                    f"first seen at line {first_lines[item.id]}"
                )
            first_lines[item.id] = idx
            items.append(item)
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

from __future__ import annotations

import json
from pathlib import Path

import pytest

from autoform_eval.dataset import DatasetError, load_jsonl


def test_load_jsonl_accepts_utf8_bom(tmp_path: Path):
    path = tmp_path / "pilot.jsonl"
    path.write_text(json.dumps(_row("a")) + "\n", encoding="utf-8-sig")

    items = load_jsonl(path)

    assert items[0].id == "a"


def test_load_jsonl_rejects_duplicate_ids_with_line_numbers(tmp_path: Path):
    path = tmp_path / "pilot.jsonl"
    _write_jsonl(path, [_row("a"), _row("a")])

    with pytest.raises(DatasetError) as excinfo:
        load_jsonl(path)

    message = str(excinfo.value)
    assert f"{path}:2" in message
    assert "duplicate id 'a'" in message
    assert "first seen at line 1" in message


def test_load_jsonl_rejects_malformed_optional_fields(tmp_path: Path):
    path = tmp_path / "pilot.jsonl"

    bad_context = _row("bad-context")
    bad_context["context"] = ["not", "a", "string"]
    _write_jsonl(path, [bad_context])
    with pytest.raises(DatasetError, match="'context' must be a string"):
        load_jsonl(path)

    bad_extra = _row("bad-extra")
    bad_extra["semantic"]["extra"] = {"mode": "strict"}
    _write_jsonl(path, [bad_extra])
    with pytest.raises(DatasetError, match="'extra' must be a string"):
        load_jsonl(path)

    bad_notes = _row("bad-notes")
    bad_notes["provenance"]["notes"] = ["generated"]
    _write_jsonl(path, [bad_notes])
    with pytest.raises(DatasetError, match="'notes' must be a string"):
        load_jsonl(path)

    bad_forbidden = _row("bad-forbidden")
    bad_forbidden["forbidden_ok"] = ""
    _write_jsonl(path, [bad_forbidden])
    with pytest.raises(DatasetError, match="'forbidden_ok' must be list\\[string\\]"):
        load_jsonl(path)


def _write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
        encoding="utf-8",
    )


def _row(item_id: str) -> dict:
    return {
        "schema_version": "1.0",
        "checker_version": "1.0",
        "id": item_id,
        "nl": "A simple proposition.",
        "imports": ["Mathlib"],
        "context": "",
        "expected": "True",
        "family": "ring_identity",
        "tier": "A",
        "split": "pilot",
        "tags": [],
        "semantic": {
            "kind": "normalized_ref",
            "check": "ring_identity_norm",
        },
        "provenance": {
            "source_kind": "other",
            "source_ref": "test",
            "license": "CC0-1.0",
        },
    }

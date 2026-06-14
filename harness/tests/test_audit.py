from __future__ import annotations

import json
from pathlib import Path

from autoform_eval.audit import audit_dataset, render_audit_markdown


def test_audit_dataset_reports_coverage_and_cross_split_duplicates(tmp_path: Path):
    dataset_dir = tmp_path / "dataset"
    dataset_dir.mkdir()
    _write_jsonl(
        dataset_dir / "pilot.jsonl",
        [
            _row("shared", "pilot", "ring_identity", nl="same nl", expected="x = x"),
            _row(
                "pilot-set", "pilot", "set_equality", nl="set nl", expected="{1} = {1}"
            ),
        ],
    )
    _write_jsonl(
        dataset_dir / "dev.jsonl",
        [
            _row("shared", "dev", "ring_identity", nl="same nl", expected="x = x"),
        ],
    )
    _write_jsonl(dataset_dir / "test.jsonl", [])

    audit = audit_dataset(dataset_dir, min_per_family_split=1)

    assert audit["total_items"] == 3
    assert audit["splits"]["pilot"]["count"] == 2
    assert audit["families"]["ring_identity"]["count"] == 2
    assert audit["duplicate_ids"] == ["shared"]
    assert audit["issue_counts"]["duplicate_id"] == 1
    assert audit["issue_counts"]["cross_split_duplicate_nl"] == 1
    assert audit["issue_counts"]["cross_split_duplicate_expected"] == 1
    assert any(gap["split"] == "test" for gap in audit["coverage_gaps"])

    markdown = render_audit_markdown(audit)
    assert "# Autoformalization Dataset Audit" in markdown
    assert "ring_identity" in markdown
    assert "duplicate_id" in markdown


def test_audit_dataset_passes_clean_minimum_free_dataset(tmp_path: Path):
    dataset_dir = tmp_path / "dataset"
    dataset_dir.mkdir()
    for split in ("pilot", "dev", "test"):
        _write_jsonl(
            dataset_dir / f"{split}.jsonl",
            [
                _row(
                    f"{split}-ring",
                    split,
                    "ring_identity",
                    nl=f"{split} ring",
                    expected=f"{split}Ring = {split}Ring",
                ),
                _row(
                    f"{split}-set",
                    split,
                    "set_equality",
                    nl=f"{split} set",
                    expected=f"{split}Set = {split}Set",
                ),
            ],
        )

    audit = audit_dataset(dataset_dir, min_per_family_split=1)

    assert audit["total_items"] == 6
    assert audit["issues"] == []
    assert audit["issue_counts"] == {}


def _write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows),
        encoding="utf-8",
    )


def _row(item_id: str, split: str, family: str, *, nl: str, expected: str) -> dict:
    check_by_family = {
        "ring_identity": "ring_identity_norm",
        "set_equality": "set_equality_norm",
    }
    return {
        "schema_version": "1.0",
        "checker_version": "1.0",
        "id": item_id,
        "nl": nl,
        "imports": [],
        "context": "",
        "expected": expected,
        "family": family,
        "tier": "A",
        "split": split,
        "tags": [],
        "semantic": {
            "kind": "normalized_ref",
            "check": check_by_family[family],
        },
        "provenance": {
            "source_kind": "assistant_generated",
            "source_ref": "test",
            "license": "MIT",
        },
    }

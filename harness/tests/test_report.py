from __future__ import annotations

import json
from pathlib import Path

import pytest

from autoform_eval.report import ResultError, compute_summary, load_results_jsonl


def test_compute_summary_excludes_provider_errors_from_rates():
    records = [
        _record("a", bucket="pass", test1_pass=True, test2_pass=True),
        _record("b", bucket="provider_error"),
    ]

    summary = compute_summary(records)

    assert summary["total_attempts"] == 2
    assert summary["evaluable_attempts"] == 1
    assert summary["provider_error_attempts"] == 1
    assert summary["combined_rate"] == 1.0
    assert summary["pass_at_k"]["groups"] == 1


def test_compute_summary_rejects_duplicate_attempt_rows():
    records = [
        _record("a", bucket="pass", test1_pass=True, test2_pass=True),
        _record("a", bucket="semantic_fail"),
    ]

    with pytest.raises(ResultError, match="duplicate attempt row"):
        compute_summary(records)


def test_compute_summary_rejects_invalid_result_fields():
    bad_bucket = _record("a", bucket="not_a_bucket")
    with pytest.raises(ResultError, match="unsupported bucket"):
        compute_summary([bad_bucket])

    bad_attempt = _record("a", bucket="pass", test1_pass=True, test2_pass=True)
    bad_attempt["attempt_index"] = "1"
    with pytest.raises(ResultError, match="positive integer"):
        compute_summary([bad_attempt])

    bad_pass = _record("a", bucket="pass", test1_pass=True, test2_pass=False)
    with pytest.raises(ResultError, match="pass bucket requires"):
        compute_summary([bad_pass])


def test_load_results_jsonl_reports_line_numbers(tmp_path: Path):
    path = tmp_path / "results.jsonl"
    path.write_text(json.dumps(_record("a")) + "\n[]\n", encoding="utf-8")

    with pytest.raises(ResultError, match=r"results\.jsonl:2"):
        load_results_jsonl(path)


def test_load_results_jsonl_accepts_utf8_bom(tmp_path: Path):
    path = tmp_path / "results.jsonl"
    path.write_text(json.dumps(_record("a")) + "\n", encoding="utf-8-sig")

    records = load_results_jsonl(path)

    assert records[0]["item_id"] == "a"


def _record(
    item_id: str,
    *,
    bucket: str = "semantic_fail",
    test1_pass: bool = False,
    test2_pass: bool = False,
    attempt_index: int = 1,
) -> dict:
    return {
        "run_id": "run",
        "item_id": item_id,
        "split": "pilot",
        "family": "ring_identity",
        "tier": "A",
        "provider": "mock",
        "model": "mock",
        "attempt_index": attempt_index,
        "bucket": bucket,
        "test1_pass": test1_pass,
        "test2_pass": test2_pass,
        "shape_pass": None,
    }

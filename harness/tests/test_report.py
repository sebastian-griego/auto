from __future__ import annotations

import json
from pathlib import Path

import pytest

from autoform_eval.report import (
    ResultError,
    compute_summary,
    load_results_jsonl,
    verify_manifest,
    write_manifest,
    write_report,
    write_summary,
)


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


def test_compute_summary_rejects_impossible_pass_flags():
    bad_order = _record("a", bucket="semantic_fail", test2_pass=True)
    with pytest.raises(ResultError, match="test2_pass requires test1_pass"):
        compute_summary([bad_order])

    bad_bucket = _record(
        "a", bucket="semantic_fail", test1_pass=True, test2_pass=True
    )
    with pytest.raises(ResultError, match="test2_pass requires pass bucket"):
        compute_summary([bad_bucket])


def test_compute_summary_rejects_malformed_artifact_fields():
    negative_elapsed = _record("a")
    negative_elapsed["test1_elapsed_ms"] = -1
    with pytest.raises(ResultError, match="test1_elapsed_ms"):
        compute_summary([negative_elapsed])

    bool_heartbeats = _record("a")
    bool_heartbeats["test2_heartbeats"] = True
    with pytest.raises(ResultError, match="test2_heartbeats"):
        compute_summary([bool_heartbeats])

    bad_hash = _record("a")
    bad_hash["candidate_hash"] = {"sha256": "abc"}
    with pytest.raises(ResultError, match="candidate_hash"):
        compute_summary([bad_hash])


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


def test_write_manifest_hashes_core_and_record_artifacts(tmp_path: Path):
    run_dir = tmp_path / "run"
    run_dir.mkdir()
    rendered = run_dir / "rendered"
    logs = run_dir / "logs"
    rendered.mkdir()
    logs.mkdir()

    record = _record("a", bucket="pass", test1_pass=True, test2_pass=True)
    record["test1_rendered_path"] = "rendered/a.test1.lean"
    record["test2_rendered_path"] = "rendered/a.test2.lean"
    record["test1_stdout_log_path"] = "logs/a.test1.stdout.log"
    record["test1_stderr_log_path"] = "logs/a.test1.stderr.log"
    record["test2_stdout_log_path"] = "logs/a.test2.stdout.log"
    record["test2_stderr_log_path"] = "logs/a.test2.stderr.log"

    for rel_path in (
        record["test1_rendered_path"],
        record["test2_rendered_path"],
        record["test1_stdout_log_path"],
        record["test1_stderr_log_path"],
        record["test2_stdout_log_path"],
        record["test2_stderr_log_path"],
    ):
        (run_dir / rel_path).write_text(rel_path, encoding="utf-8")

    records = [record]
    summary = compute_summary(records)
    (run_dir / "results.jsonl").write_text(
        json.dumps(record, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_summary(run_dir / "summary.json", summary)
    write_report(run_dir / "report.md", records, summary)

    manifest = write_manifest(
        run_dir, records, summary, require_record_artifacts=True
    )

    summary_bytes = (run_dir / "summary.json").read_bytes()
    assert summary_bytes.endswith(b"\n")
    assert b"\r\n" not in summary_bytes
    report_bytes = (run_dir / "report.md").read_bytes()
    assert report_bytes.endswith(b"\n")
    assert b"\r\n" not in report_bytes
    manifest_bytes = (run_dir / "manifest.json").read_bytes()
    assert manifest_bytes.endswith(b"\n")
    assert b"\r\n" not in manifest_bytes

    paths = {entry["path"] for entry in manifest["artifacts"]}
    assert {"results.jsonl", "summary.json", "report.md"}.issubset(paths)
    assert "rendered/a.test1.lean" in paths
    assert manifest["missing_record_artifacts"] == []
    verified = verify_manifest(run_dir)
    assert verified["run_id"] == "run"


def test_write_manifest_rejects_mixed_run_ids(tmp_path: Path):
    run_dir = tmp_path / "run"
    run_dir.mkdir()
    first = _record("a")
    second = _record("b")
    second["run_id"] = "other"
    records = [first, second]
    summary = compute_summary(records)

    with pytest.raises(ResultError, match="exactly one run_id"):
        write_manifest(run_dir, records, summary)


def test_write_manifest_rejects_run_dir_mismatch(tmp_path: Path):
    run_dir = tmp_path / "copied"
    run_dir.mkdir()
    records = [_record("a")]
    summary = compute_summary(records)

    with pytest.raises(ResultError, match="does not match run directory"):
        write_manifest(run_dir, records, summary)


def test_verify_manifest_rejects_mismatched_manifest_run_id(tmp_path: Path):
    run_dir = tmp_path / "run"
    run_dir.mkdir()
    record = _record("a")
    records = [record]
    summary = compute_summary(records)
    (run_dir / "results.jsonl").write_text(
        json.dumps(record, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_summary(run_dir / "summary.json", summary)
    write_report(run_dir / "report.md", records, summary)
    write_manifest(run_dir, records, summary)

    manifest_path = run_dir / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["run_id"] = "other"
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    with pytest.raises(ResultError, match="does not match run directory"):
        verify_manifest(run_dir)


def test_verify_manifest_detects_modified_artifact(tmp_path: Path):
    run_dir = tmp_path / "run"
    run_dir.mkdir()
    record = _record("a")
    records = [record]
    summary = compute_summary(records)
    (run_dir / "results.jsonl").write_text(
        json.dumps(record, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_summary(run_dir / "summary.json", summary)
    write_report(run_dir / "report.md", records, summary)
    write_manifest(run_dir, records, summary)

    (run_dir / "report.md").write_text("tampered\n", encoding="utf-8")

    with pytest.raises(ResultError, match="mismatch"):
        verify_manifest(run_dir)


def test_verify_manifest_rejects_missing_record_artifacts_by_default(
    tmp_path: Path,
):
    run_dir = tmp_path / "run"
    run_dir.mkdir()
    record = _record("a")
    record["test1_rendered_path"] = "rendered/a.test1.lean"
    records = [record]
    summary = compute_summary(records)
    (run_dir / "results.jsonl").write_text(
        json.dumps(record, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_summary(run_dir / "summary.json", summary)
    write_report(run_dir / "report.md", records, summary)
    write_manifest(run_dir, records, summary)

    with pytest.raises(ResultError, match="missing referenced record artifacts"):
        verify_manifest(run_dir)

    verified = verify_manifest(run_dir, allow_missing_record_artifacts=True)
    assert verified["missing_record_artifacts"] == ["rendered/a.test1.lean"]


def test_verify_manifest_rejects_unlisted_artifacts_by_default(tmp_path: Path):
    run_dir = tmp_path / "run"
    run_dir.mkdir()
    record = _record("a")
    records = [record]
    summary = compute_summary(records)
    (run_dir / "results.jsonl").write_text(
        json.dumps(record, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_summary(run_dir / "summary.json", summary)
    write_report(run_dir / "report.md", records, summary)
    write_manifest(run_dir, records, summary)
    (run_dir / "debug.txt").write_text("not captured\n", encoding="utf-8")

    with pytest.raises(ResultError, match="unexpected artifacts not in manifest"):
        verify_manifest(run_dir)

    verified = verify_manifest(run_dir, allow_extra_artifacts=True)
    assert verified["run_id"] == "run"


def test_verify_manifest_rejects_nested_unlisted_manifest(tmp_path: Path):
    run_dir = tmp_path / "run"
    run_dir.mkdir()
    record = _record("a")
    records = [record]
    summary = compute_summary(records)
    (run_dir / "results.jsonl").write_text(
        json.dumps(record, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_summary(run_dir / "summary.json", summary)
    write_report(run_dir / "report.md", records, summary)
    write_manifest(run_dir, records, summary)
    (run_dir / "nested").mkdir()
    (run_dir / "nested" / "manifest.json").write_text("extra\n", encoding="utf-8")

    with pytest.raises(ResultError, match="nested/manifest\\.json"):
        verify_manifest(run_dir)


def test_write_manifest_rejects_escaping_record_artifact_path(tmp_path: Path):
    run_dir = tmp_path / "run"
    run_dir.mkdir()
    record = _record("a")
    record["test1_rendered_path"] = "../outside.lean"
    records = [record]
    summary = compute_summary(records)
    (run_dir / "results.jsonl").write_text(
        json.dumps(record, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_summary(run_dir / "summary.json", summary)
    write_report(run_dir / "report.md", records, summary)

    with pytest.raises(ResultError, match="run directory"):
        write_manifest(run_dir, records, summary)


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

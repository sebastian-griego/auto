import json
from pathlib import Path

from autoform_eval.cache import JsonCache
from autoform_eval.cli import (
    _parse_models,
    _prepare_run_dir,
    _run_attempt,
    _write_run_text,
    main,
)
from autoform_eval.types import DatasetItem, ProvenanceSpec, SemanticSpec


def test_write_run_text_canonicalizes_newlines(tmp_path: Path):
    path = tmp_path / "artifact.log"

    _write_run_text(path, "alpha\r\nbeta\rgamma\n")

    assert path.read_bytes() == b"alpha\nbeta\ngamma\n"


def test_prepare_run_dir_suffixes_automatic_timestamp_collisions(
    monkeypatch, tmp_path: Path
):
    monkeypatch.setattr("autoform_eval.cli._mk_run_id", lambda: "20260615_120000")
    first = tmp_path / "results" / "20260615_120000"
    first.mkdir(parents=True)

    run_id, run_dir = _prepare_run_dir(tmp_path / "results")

    assert run_id == "20260615_120000_01"
    assert run_dir == tmp_path / "results" / "20260615_120000_01"
    assert run_dir.is_dir()


def test_prepare_run_dir_rejects_existing_explicit_run_id(tmp_path: Path):
    (tmp_path / "results" / "paper").mkdir(parents=True)

    try:
        _prepare_run_dir(tmp_path / "results", "paper")
    except ValueError as exc:
        assert "run_id already exists: paper" in str(exc)
    else:
        raise AssertionError("expected explicit run_id collision to fail")


def test_prepare_run_dir_rejects_unsafe_run_id(tmp_path: Path):
    try:
        _prepare_run_dir(tmp_path / "results", "../escape")
    except ValueError as exc:
        assert "run_id must start with" in str(exc)
    else:
        raise AssertionError("expected unsafe run_id to fail")
    assert not (tmp_path / "results").exists()


def test_parse_models_rejects_duplicate_model_specs():
    try:
        _parse_models("openai:mock, OpenAI:mock")
    except ValueError as exc:
        message = str(exc)
        assert "duplicate model token OpenAI:mock" in message
        assert "position 2" in message
        assert "first seen at position 1" in message
    else:
        raise AssertionError("expected duplicate model spec to fail")


def test_parse_models_rejects_empty_provider_or_model():
    for raw in (":mock", "openai:"):
        try:
            _parse_models(raw)
        except ValueError as exc:
            assert "expected provider:model" in str(exc)
        else:
            raise AssertionError(f"expected invalid model spec to fail: {raw}")


def test_run_rejects_invalid_config_before_creating_run_dir(tmp_path: Path):
    dataset_dir = tmp_path / "dataset"
    _write_dataset_split(dataset_dir)
    results_root = tmp_path / "results"

    cases = [
        ["--models", "openai:mock,openai:mock"],
        ["--models", "openai:mock", "--k", "0"],
        ["--models", "openai:mock", "--prompt-version", "bad-version"],
    ]
    for extra_args in cases:
        exit_code = main(
            [
                "run",
                "--split",
                "pilot",
                "--dataset-dir",
                str(dataset_dir),
                "--results-root",
                str(results_root),
                "--mock",
                *extra_args,
            ]
        )

        assert exit_code == 2
        assert not results_root.exists()


def test_run_attempt_records_test1_runner_exception_artifacts(
    monkeypatch, tmp_path: Path
):
    lean_dir = tmp_path / "lean"
    _write_templates(lean_dir)
    run_dir = tmp_path / "run"

    def fail_runner(*_args, **_kwargs):
        raise RuntimeError("lean unavailable")

    monkeypatch.setattr("autoform_eval.cli.run_lean_file", fail_runner)

    attempt = _run_attempt(
        item=_dataset_item(),
        provider="openai",
        model="mock",
        params={"temperature": 0.0, "max_output_tokens": 64},
        k_index=1,
        lean_dir=lean_dir,
        run_dir=run_dir,
        cache=JsonCache(tmp_path / "cache"),
        timeout1_s=1.0,
        timeout2_s=1.0,
        hb1=1000,
        hb2=1000,
        mock=True,
        save_prompt_text=False,
        prompt_version="v1.1.0",
        provider_retries=0,
        provider_retry_backoff_s=0.0,
    )

    assert attempt["bucket"] == "elab_fail"
    assert attempt["test1_pass"] is False
    assert attempt["test1_rendered_path"] == "rendered/unit.openai.mock.k1.test1.lean"
    assert (
        attempt["test1_stderr_log_path"]
        == "logs/unit.openai.mock.k1.test1.stderr.log"
    )
    assert (
        attempt["test1_stdout_log_path"]
        == "logs/unit.openai.mock.k1.test1.stdout.log"
    )
    assert attempt["test2_rendered_path"] == ""
    assert (run_dir / attempt["test1_rendered_path"]).exists()
    assert (
        run_dir / attempt["test1_stderr_log_path"]
    ).read_text(encoding="utf-8") == "runner_exception:RuntimeError:lean unavailable"
    assert (run_dir / attempt["test1_stdout_log_path"]).read_bytes() == b""


def test_report_rejects_run_id_mismatch_before_writing_artifacts(tmp_path: Path):
    run_dir = tmp_path / "copied"
    run_dir.mkdir()
    record = {
        "run_id": "original",
        "item_id": "a",
        "split": "pilot",
        "family": "ring_identity",
        "tier": "A",
        "provider": "mock",
        "model": "mock",
        "attempt_index": 1,
        "bucket": "semantic_fail",
        "test1_pass": False,
        "test2_pass": False,
        "shape_pass": None,
    }
    (run_dir / "results.jsonl").write_text(
        json.dumps(record, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    exit_code = main(["report", "--run-dir", str(run_dir)])

    assert exit_code == 2
    assert not (run_dir / "summary.json").exists()
    assert not (run_dir / "report.md").exists()
    assert not (run_dir / "manifest.json").exists()


def _write_templates(lean_dir: Path) -> None:
    template_dir = lean_dir / "AutoformalizationEval" / "Template"
    template_dir.mkdir(parents=True)
    (template_dir / "Test1.lean.template").write_text(
        "{{IMPORTS}}\n{{CONTEXT}}\n#check ({{CAND}})\n-- {{HEARTBEATS}}\n",
        encoding="utf-8",
    )
    (template_dir / "Test2.lean.template").write_text(
        "\n".join(
            [
                "{{IMPORTS}}",
                "{{CONTEXT}}",
                "#check ({{CAND}})",
                "#check ({{EXPECTED}})",
                "-- {{FAMILY}} {{CHECK_KEY}} {{FRAGMENT_KEY}}",
                "-- {{ENUM_CAP}} {{HEARTBEATS}}",
                "",
            ]
        ),
        encoding="utf-8",
    )


def _write_dataset_split(dataset_dir: Path) -> None:
    dataset_dir.mkdir(parents=True)
    row = {
        "schema_version": "1.0",
        "checker_version": "1.0",
        "id": "unit",
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
    (dataset_dir / "pilot.jsonl").write_text(
        json.dumps(row, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _dataset_item() -> DatasetItem:
    return DatasetItem(
        schema_version="1.0",
        checker_version="1.0",
        id="unit",
        nl="Every natural number is equal to itself.",
        imports=["Mathlib"],
        context="",
        expected="forall a : Nat, a = a",
        family="ring_identity",
        tier="A",
        split="pilot",
        tags=[],
        semantic=SemanticSpec(kind="normalized_ref", check="ring_identity_norm"),
        provenance=ProvenanceSpec(
            source_kind="assistant_generated",
            source_ref="test",
            license="MIT",
        ),
        forbidden_ok=[],
    )

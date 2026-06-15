from __future__ import annotations

import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path, PurePosixPath
from typing import Any, get_args

from .types import Bucket


MANIFEST_SCHEMA_VERSION = 1
MANIFEST_NAME = "manifest.json"
CORE_ARTIFACT_PATHS = ("results.jsonl", "summary.json", "report.md")
VALID_BUCKETS = set(get_args(Bucket))
REQUIRED_STR_FIELDS = (
    "run_id",
    "item_id",
    "split",
    "family",
    "tier",
    "provider",
    "model",
    "bucket",
)
REQUIRED_BOOL_FIELDS = ("test1_pass", "test2_pass")
OPTIONAL_STR_FIELDS = (
    "candidate_raw",
    "candidate_hash",
    "prompt_hash",
    "prompt_version",
    "fragment_key",
    "lean_toolchain",
    "mathlib_rev",
    "stdout_excerpt",
    "stderr_excerpt",
    "prompt_text",
    "test1_rendered_path",
    "test2_rendered_path",
    "test1_stdout_log_path",
    "test1_stderr_log_path",
    "test2_stdout_log_path",
    "test2_stderr_log_path",
)
OPTIONAL_NONNEGATIVE_INT_FIELDS = (
    "test1_elapsed_ms",
    "test2_elapsed_ms",
    "test1_heartbeats",
    "test2_heartbeats",
)
RESULT_ARTIFACT_PATH_FIELDS = (
    "test1_rendered_path",
    "test2_rendered_path",
    "test1_stdout_log_path",
    "test1_stderr_log_path",
    "test2_stdout_log_path",
    "test2_stderr_log_path",
)


class ResultError(ValueError):
    pass


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _validate_relative_artifact_path(value: str, *, where: str) -> str:
    if not isinstance(value, str) or not value:
        raise ResultError(f"{where}: artifact path must be a non-empty string")
    if "\\" in value:
        raise ResultError(
            f"{where}: artifact path '{value}' must use forward slashes"
        )
    rel = PurePosixPath(value)
    if rel.is_absolute():
        raise ResultError(f"{where}: artifact path '{value}' must be relative")
    normalized = rel.as_posix()
    if normalized != value:
        raise ResultError(f"{where}: artifact path '{value}' must be normalized")
    if any(part in {"", ".", ".."} or ":" in part for part in rel.parts):
        raise ResultError(
            f"{where}: artifact path '{value}' must stay inside the run directory"
        )
    return normalized


def _path_in_run_dir(run_dir: Path, rel_path: str) -> Path:
    rel = PurePosixPath(rel_path)
    return run_dir.joinpath(*rel.parts)


def _manifest_entry(run_dir: Path, rel_path: str) -> dict[str, Any]:
    path = _path_in_run_dir(run_dir, rel_path)
    return {
        "path": rel_path,
        "bytes": path.stat().st_size,
        "sha256": _sha256_file(path),
    }


def _record_artifact_paths(
    records: list[dict[str, Any]], *, source: str = "records"
) -> list[str]:
    paths: set[str] = set()
    for idx, row in enumerate(records, 1):
        for field in RESULT_ARTIFACT_PATH_FIELDS:
            value = row.get(field)
            if not value:
                continue
            paths.add(
                _validate_relative_artifact_path(
                    value, where=f"{source}:{idx}:{field}"
                )
            )
    return sorted(paths)


def _run_artifact_paths(run_dir: Path) -> set[str]:
    paths: set[str] = set()
    for path in run_dir.rglob("*"):
        if not path.is_file():
            continue
        rel_path = path.relative_to(run_dir).as_posix()
        if rel_path == MANIFEST_NAME:
            continue
        paths.add(
            _validate_relative_artifact_path(
                rel_path, where=f"{run_dir}:artifact"
            )
        )
    return paths


def _rate(num: int, den: int) -> float:
    return 0.0 if den == 0 else num / den


def _as_attempt_index(value: Any) -> int:
    try:
        out = int(value)
    except (TypeError, ValueError):
        return 1
    return out if out >= 1 else 1


def _is_provider_error(row: dict[str, Any]) -> bool:
    return str(row.get("bucket", "")) == "provider_error"


def load_results_jsonl(path: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8-sig") as f:
        for line_no, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ResultError(f"{path}:{line_no}: invalid JSON: {exc}") from exc
            if not isinstance(row, dict):
                raise ResultError(f"{path}:{line_no}: each row must be a JSON object")
            records.append(row)
    validate_result_records(records, source=str(path))
    return records


def validate_result_records(
    records: list[dict[str, Any]], *, source: str = "records"
) -> None:
    seen_attempts: dict[tuple[str, str, str, str, str, str, int], int] = {}
    for idx, row in enumerate(records, 1):
        where = f"{source}:{idx}"
        for field in REQUIRED_STR_FIELDS:
            value = row.get(field)
            if not isinstance(value, str) or not value:
                raise ResultError(f"{where}: '{field}' must be a non-empty string")

        bucket = row["bucket"]
        if bucket not in VALID_BUCKETS:
            valid = ", ".join(sorted(VALID_BUCKETS))
            raise ResultError(
                f"{where}: unsupported bucket '{bucket}' (valid: {valid})"
            )

        for field in REQUIRED_BOOL_FIELDS:
            if not isinstance(row.get(field), bool):
                raise ResultError(f"{where}: '{field}' must be a boolean")

        if (
            "shape_pass" in row
            and row["shape_pass"] is not None
            and not isinstance(row["shape_pass"], bool)
        ):
            raise ResultError(f"{where}: 'shape_pass' must be a boolean or null")

        for field in OPTIONAL_STR_FIELDS:
            if field in row and not isinstance(row[field], str):
                raise ResultError(f"{where}: '{field}' must be a string")

        for field in OPTIONAL_NONNEGATIVE_INT_FIELDS:
            value = row.get(field)
            if value is None:
                continue
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                raise ResultError(
                    f"{where}: '{field}' must be a non-negative integer"
                )

        attempt_index = row.get("attempt_index")
        if (
            not isinstance(attempt_index, int)
            or isinstance(attempt_index, bool)
            or attempt_index < 1
        ):
            raise ResultError(f"{where}: 'attempt_index' must be a positive integer")

        if bucket == "pass" and not (row["test1_pass"] and row["test2_pass"]):
            raise ResultError(
                f"{where}: pass bucket requires test1_pass and test2_pass"
            )
        if row["test2_pass"] and not row["test1_pass"]:
            raise ResultError(f"{where}: test2_pass requires test1_pass")
        if row["test2_pass"] and bucket != "pass":
            raise ResultError(f"{where}: test2_pass requires pass bucket")
        if bucket == "provider_error" and (row["test1_pass"] or row["test2_pass"]):
            raise ResultError(
                f"{where}: provider_error bucket cannot pass Lean checks"
            )

        attempt_key = (
            row["run_id"],
            row["provider"],
            row["model"],
            row["split"],
            row["item_id"],
            attempt_index,
        )
        if attempt_key in seen_attempts:
            first_idx = seen_attempts[attempt_key]
            raise ResultError(
                f"{where}: duplicate attempt row; first seen at {source}:{first_idx}"
            )
        seen_attempts[attempt_key] = idx


def _pass_at_k(records: list[dict[str, Any]], key_fields: tuple[str, ...]) -> dict[str, Any]:
    grouped: dict[tuple[str, ...], list[tuple[int, bool]]] = defaultdict(list)
    max_k = 1
    for row in records:
        key = tuple(str(row.get(field, "")) for field in key_fields)
        k = _as_attempt_index(row.get("attempt_index", 1))
        grouped[key].append((k, str(row.get("bucket", "")) == "pass"))
        if k > max_k:
            max_k = k

    if not grouped:
        return {"max_k": 0, "groups": 0, "rates": {}}

    rates: dict[str, float] = {}
    for k in range(1, max_k + 1):
        success = 0
        for attempts in grouped.values():
            if any(is_pass for attempt_k, is_pass in attempts if attempt_k <= k):
                success += 1
        rates[str(k)] = _rate(success, len(grouped))
    return {"max_k": max_k, "groups": len(grouped), "rates": rates}


def _combined_by_key(records: list[dict[str, Any]], field: str) -> dict[str, dict[str, Any]]:
    counts: dict[str, dict[str, int]] = defaultdict(lambda: {"total": 0, "pass": 0})
    for row in records:
        key = str(row.get(field, "unknown"))
        counts[key]["total"] += 1
        if str(row.get("bucket", "")) == "pass":
            counts[key]["pass"] += 1
    return {
        k: {"total": v["total"], "combined_rate": _rate(v["pass"], v["total"])}
        for k, v in sorted(counts.items())
    }


def compute_summary(records: list[dict[str, Any]]) -> dict[str, Any]:
    validate_result_records(records)
    total = len(records)
    evaluable_records = [r for r in records if not _is_provider_error(r)]
    evaluable_total = len(evaluable_records)
    provider_error_attempts = total - evaluable_total
    t1 = sum(1 for r in evaluable_records if r.get("test1_pass"))
    t2 = sum(1 for r in evaluable_records if r.get("test2_pass"))
    combined = sum(1 for r in evaluable_records if r.get("bucket") == "pass")

    by_bucket = Counter()
    for r in records:
        bucket = str(r.get("bucket", "unknown"))
        by_bucket[bucket] += 1

    by_model_records: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in records:
        provider = str(row.get("provider", "unknown"))
        model = str(row.get("model", "unknown"))
        by_model_records[f"{provider}:{model}"].append(row)

    by_model: dict[str, dict[str, Any]] = {}
    for model_key, rows in sorted(by_model_records.items()):
        model_evaluable_rows = [r for r in rows if not _is_provider_error(r)]
        model_provider_error_attempts = len(rows) - len(model_evaluable_rows)
        model_t1 = sum(1 for r in model_evaluable_rows if r.get("test1_pass"))
        model_t2 = sum(1 for r in model_evaluable_rows if r.get("test2_pass"))
        model_combined = sum(1 for r in model_evaluable_rows if r.get("bucket") == "pass")
        model_items = len({str(r.get("item_id", "")) for r in rows})
        model_bucket = Counter(str(r.get("bucket", "unknown")) for r in rows)
        by_model[model_key] = {
            "total_attempts": len(rows),
            "evaluable_attempts": len(model_evaluable_rows),
            "provider_error_attempts": model_provider_error_attempts,
            "items": model_items,
            "test1_rate": _rate(model_t1, len(model_evaluable_rows)),
            "test2_rate": _rate(model_t2, len(model_evaluable_rows)),
            "combined_rate": _rate(model_combined, len(model_evaluable_rows)),
            "pass_at_k": _pass_at_k(model_evaluable_rows, key_fields=("item_id",)),
            "by_bucket": dict(model_bucket),
            "by_family": _combined_by_key(model_evaluable_rows, "family"),
            "by_tier": _combined_by_key(model_evaluable_rows, "tier"),
            "by_split": _combined_by_key(model_evaluable_rows, "split"),
        }

    return {
        "total": total,
        "total_attempts": total,
        "evaluable_attempts": evaluable_total,
        "provider_error_attempts": provider_error_attempts,
        "provider_error_rate": _rate(provider_error_attempts, total),
        "test1_rate": _rate(t1, evaluable_total),
        "test2_rate": _rate(t2, evaluable_total),
        "combined_rate": _rate(combined, evaluable_total),
        "pass_at_k": _pass_at_k(evaluable_records, key_fields=("provider", "model", "item_id")),
        "by_family": _combined_by_key(evaluable_records, "family"),
        "by_tier": _combined_by_key(evaluable_records, "tier"),
        "by_split": _combined_by_key(evaluable_records, "split"),
        "by_bucket": dict(by_bucket),
        "by_model": by_model,
    }


def write_summary(path: Path, summary: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    _write_text(path, json.dumps(summary, indent=2, sort_keys=True) + "\n")


def write_report(path: Path, records: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    lines: list[str] = []
    lines.append("# Autoformalization Eval Report")
    lines.append("")
    lines.append("## Overall")
    lines.append("")
    lines.append(f"- Total attempts: {summary['total_attempts']}")
    lines.append(f"- Evaluable attempts (exclude provider errors): {summary.get('evaluable_attempts', 0)}")
    lines.append(f"- Provider error attempts: {summary.get('provider_error_attempts', 0)}")
    lines.append(f"- Provider error rate: {float(summary.get('provider_error_rate', 0.0)):.3f}")
    lines.append(f"- Test1 rate (evaluable only): {summary['test1_rate']:.3f}")
    lines.append(f"- Test2 rate (evaluable only): {summary['test2_rate']:.3f}")
    lines.append(f"- Combined rate (evaluable only): {summary['combined_rate']:.3f}")
    pass_at_k = summary.get("pass_at_k", {})
    rates = pass_at_k.get("rates", {})
    if rates:
        max_k = pass_at_k.get("max_k", 1)
        lines.append(f"- Pass@{max_k} (evaluable only): {float(rates.get(str(max_k), 0.0)):.3f}")
    lines.append("")
    lines.append("## Model Table")
    lines.append("")
    lines.append("| Model | Attempts | Evaluable | ProviderErr | Items | Test1 | Test2 | Combined | Pass@k(max) |")
    lines.append("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
    for model_key, model_summary in summary.get("by_model", {}).items():
        model_pass = model_summary.get("pass_at_k", {})
        model_rates = model_pass.get("rates", {})
        model_max_k = int(model_pass.get("max_k", 1))
        model_pass_max = float(model_rates.get(str(model_max_k), 0.0))
        lines.append(
            "| "
            f"{model_key} | "
            f"{int(model_summary.get('total_attempts', 0))} | "
            f"{int(model_summary.get('evaluable_attempts', 0))} | "
            f"{int(model_summary.get('provider_error_attempts', 0))} | "
            f"{int(model_summary.get('items', 0))} | "
            f"{float(model_summary.get('test1_rate', 0.0)):.3f} | "
            f"{float(model_summary.get('test2_rate', 0.0)):.3f} | "
            f"{float(model_summary.get('combined_rate', 0.0)):.3f} | "
            f"{model_pass_max:.3f} |"
        )

    lines.append("")
    lines.append("## Family Slice")
    lines.append("")
    for fam, stats in summary.get("by_family", {}).items():
        lines.append(f"- {fam}: total={int(stats.get('total', 0))} combined={float(stats.get('combined_rate', 0.0)):.3f}")

    lines.append("")
    lines.append("## Tier Slice")
    lines.append("")
    for tier, stats in summary.get("by_tier", {}).items():
        lines.append(f"- {tier}: total={int(stats.get('total', 0))} combined={float(stats.get('combined_rate', 0.0)):.3f}")

    lines.append("")
    lines.append("## Buckets")
    lines.append("")
    for bucket, count in sorted(summary["by_bucket"].items()):
        lines.append(f"- {bucket}: {count}")

    lines.append("")
    lines.append("## Sample failures")
    lines.append("")
    shown = 0
    for row in records:
        if row.get("bucket") == "pass":
            continue
        stderr_excerpt = str(row.get("stderr_excerpt", "")).strip()
        stdout_excerpt = str(row.get("stdout_excerpt", "")).strip()
        lean_output = stderr_excerpt if stderr_excerpt else stdout_excerpt
        lines.append(f"- item `{row.get('item_id')}` bucket `{row.get('bucket')}`")
        lines.append(f"  - candidate: `{row.get('candidate_raw', '')[:120]}`")
        lines.append(f"  - lean_output: `{lean_output[:180]}`")
        lines.append(f"  - stderr_excerpt: `{stderr_excerpt[:180]}`")
        lines.append(f"  - stdout_excerpt: `{stdout_excerpt[:180]}`")
        shown += 1
        if shown >= 10:
            break

    path.parent.mkdir(parents=True, exist_ok=True)
    _write_text(path, "\n".join(lines) + "\n")


def write_manifest(
    run_dir: Path,
    records: list[dict[str, Any]],
    summary: dict[str, Any],
    *,
    require_record_artifacts: bool = False,
) -> dict[str, Any]:
    validate_result_records(records)

    artifact_paths: set[str] = set()
    for rel_path in CORE_ARTIFACT_PATHS:
        if _path_in_run_dir(run_dir, rel_path).exists():
            artifact_paths.add(rel_path)

    missing_record_artifacts: list[str] = []
    for rel_path in _record_artifact_paths(records):
        if _path_in_run_dir(run_dir, rel_path).exists():
            artifact_paths.add(rel_path)
        else:
            missing_record_artifacts.append(rel_path)

    if missing_record_artifacts and require_record_artifacts:
        missing = ", ".join(missing_record_artifacts[:5])
        extra = "" if len(missing_record_artifacts) <= 5 else ", ..."
        raise ResultError(f"missing referenced run artifacts: {missing}{extra}")

    manifest = {
        "schema_version": MANIFEST_SCHEMA_VERSION,
        "run_id": _manifest_run_id(records),
        "total_attempts": int(summary.get("total_attempts", len(records))),
        "artifacts": [
            _manifest_entry(run_dir, rel_path) for rel_path in sorted(artifact_paths)
        ],
        "missing_record_artifacts": missing_record_artifacts,
    }
    manifest_path = run_dir / MANIFEST_NAME
    _write_text(manifest_path, json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    return manifest


def _write_text(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8", newline="\n")


def verify_manifest(
    run_dir: Path,
    *,
    allow_missing_record_artifacts: bool = False,
    allow_extra_artifacts: bool = False,
) -> dict[str, Any]:
    manifest_path = run_dir / MANIFEST_NAME
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8-sig"))
    except FileNotFoundError as exc:
        raise ResultError(f"missing {manifest_path}") from exc
    except json.JSONDecodeError as exc:
        raise ResultError(f"{manifest_path}: invalid JSON: {exc}") from exc

    if not isinstance(manifest, dict):
        raise ResultError(f"{manifest_path}: manifest must be a JSON object")
    if manifest.get("schema_version") != MANIFEST_SCHEMA_VERSION:
        raise ResultError(
            f"{manifest_path}: unsupported schema_version {manifest.get('schema_version')!r}"
        )

    artifacts = manifest.get("artifacts")
    if not isinstance(artifacts, list) or not artifacts:
        raise ResultError(f"{manifest_path}: artifacts must be a non-empty list")

    seen_paths: set[str] = set()
    for idx, entry in enumerate(artifacts, 1):
        where = f"{manifest_path}:artifacts:{idx}"
        if not isinstance(entry, dict):
            raise ResultError(f"{where}: artifact entry must be an object")
        rel_path = _validate_relative_artifact_path(
            entry.get("path", ""), where=where
        )
        if rel_path == MANIFEST_NAME:
            raise ResultError(f"{where}: manifest cannot hash itself")
        if rel_path in seen_paths:
            raise ResultError(f"{where}: duplicate artifact path '{rel_path}'")
        seen_paths.add(rel_path)

        path = _path_in_run_dir(run_dir, rel_path)
        if not path.exists():
            raise ResultError(f"{where}: missing artifact '{rel_path}'")

        expected_bytes = entry.get("bytes")
        if (
            not isinstance(expected_bytes, int)
            or isinstance(expected_bytes, bool)
            or expected_bytes < 0
        ):
            raise ResultError(f"{where}: bytes must be a non-negative integer")
        actual_bytes = path.stat().st_size
        if actual_bytes != expected_bytes:
            raise ResultError(
                f"{where}: byte size mismatch for '{rel_path}' "
                f"(expected {expected_bytes}, got {actual_bytes})"
            )

        expected_hash = entry.get("sha256")
        if not isinstance(expected_hash, str) or not _looks_like_sha256(expected_hash):
            raise ResultError(f"{where}: sha256 must be a 64-character hex string")
        actual_hash = _sha256_file(path)
        if actual_hash != expected_hash:
            raise ResultError(f"{where}: sha256 mismatch for '{rel_path}'")

    missing = manifest.get("missing_record_artifacts", [])
    if not isinstance(missing, list):
        raise ResultError(
            f"{manifest_path}: missing_record_artifacts must be a list"
        )
    for idx, rel_path in enumerate(missing, 1):
        _validate_relative_artifact_path(
            rel_path, where=f"{manifest_path}:missing_record_artifacts:{idx}"
        )
    if missing and not allow_missing_record_artifacts:
        shown = ", ".join(missing[:5])
        suffix = "" if len(missing) <= 5 else ", ..."
        raise ResultError(
            f"{manifest_path}: missing referenced record artifacts: {shown}{suffix}"
        )

    if not allow_extra_artifacts:
        extra_paths = sorted(_run_artifact_paths(run_dir) - seen_paths)
        if extra_paths:
            shown = ", ".join(extra_paths[:5])
            suffix = "" if len(extra_paths) <= 5 else ", ..."
            raise ResultError(
                f"{manifest_path}: unexpected artifacts not in manifest: "
                f"{shown}{suffix}"
            )

    return manifest


def _manifest_run_id(records: list[dict[str, Any]]) -> str:
    run_ids = sorted(
        {str(row.get("run_id", "")) for row in records if row.get("run_id")}
    )
    return run_ids[0] if len(run_ids) == 1 else ""


def _looks_like_sha256(value: str) -> bool:
    if len(value) != 64:
        return False
    return all(char in "0123456789abcdef" for char in value.lower())

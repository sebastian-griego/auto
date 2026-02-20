from __future__ import annotations

import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


def _rate(num: int, den: int) -> float:
    return 0.0 if den == 0 else num / den


def _as_attempt_index(value: Any) -> int:
    try:
        out = int(value)
    except (TypeError, ValueError):
        return 1
    return out if out >= 1 else 1


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
    total = len(records)
    t1 = sum(1 for r in records if r.get("test1_pass"))
    t2 = sum(1 for r in records if r.get("test2_pass"))
    combined = sum(1 for r in records if r.get("bucket") == "pass")

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
        model_t1 = sum(1 for r in rows if r.get("test1_pass"))
        model_t2 = sum(1 for r in rows if r.get("test2_pass"))
        model_combined = sum(1 for r in rows if r.get("bucket") == "pass")
        model_items = len({str(r.get("item_id", "")) for r in rows})
        model_bucket = Counter(str(r.get("bucket", "unknown")) for r in rows)
        by_model[model_key] = {
            "total_attempts": len(rows),
            "items": model_items,
            "test1_rate": _rate(model_t1, len(rows)),
            "test2_rate": _rate(model_t2, len(rows)),
            "combined_rate": _rate(model_combined, len(rows)),
            "pass_at_k": _pass_at_k(rows, key_fields=("item_id",)),
            "by_bucket": dict(model_bucket),
            "by_family": _combined_by_key(rows, "family"),
            "by_tier": _combined_by_key(rows, "tier"),
            "by_split": _combined_by_key(rows, "split"),
        }

    return {
        "total": total,
        "total_attempts": total,
        "test1_rate": _rate(t1, total),
        "test2_rate": _rate(t2, total),
        "combined_rate": _rate(combined, total),
        "pass_at_k": _pass_at_k(records, key_fields=("provider", "model", "item_id")),
        "by_family": _combined_by_key(records, "family"),
        "by_tier": _combined_by_key(records, "tier"),
        "by_split": _combined_by_key(records, "split"),
        "by_bucket": dict(by_bucket),
        "by_model": by_model,
    }


def write_summary(path: Path, summary: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_report(path: Path, records: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    lines: list[str] = []
    lines.append("# Autoformalization Eval Report")
    lines.append("")
    lines.append("## Overall")
    lines.append("")
    lines.append(f"- Total attempts: {summary['total_attempts']}")
    lines.append(f"- Test1 rate: {summary['test1_rate']:.3f}")
    lines.append(f"- Test2 rate: {summary['test2_rate']:.3f}")
    lines.append(f"- Combined rate: {summary['combined_rate']:.3f}")
    pass_at_k = summary.get("pass_at_k", {})
    rates = pass_at_k.get("rates", {})
    if rates:
        max_k = pass_at_k.get("max_k", 1)
        lines.append(f"- Pass@{max_k}: {float(rates.get(str(max_k), 0.0)):.3f}")
    lines.append("")
    lines.append("## Model Table")
    lines.append("")
    lines.append("| Model | Attempts | Items | Test1 | Test2 | Combined | Pass@k(max) |")
    lines.append("|---|---:|---:|---:|---:|---:|---:|")
    for model_key, model_summary in summary.get("by_model", {}).items():
        model_pass = model_summary.get("pass_at_k", {})
        model_rates = model_pass.get("rates", {})
        model_max_k = int(model_pass.get("max_k", 1))
        model_pass_max = float(model_rates.get(str(model_max_k), 0.0))
        lines.append(
            "| "
            f"{model_key} | "
            f"{int(model_summary.get('total_attempts', 0))} | "
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
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")

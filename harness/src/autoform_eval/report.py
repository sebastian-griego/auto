from __future__ import annotations

import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


def _rate(num: int, den: int) -> float:
    return 0.0 if den == 0 else num / den


def compute_summary(records: list[dict[str, Any]]) -> dict[str, Any]:
    total = len(records)
    t1 = sum(1 for r in records if r.get("test1_pass"))
    t2 = sum(1 for r in records if r.get("test2_pass"))
    combined = sum(1 for r in records if r.get("bucket") == "pass")

    by_family: dict[str, dict[str, Any]] = defaultdict(lambda: {"total": 0, "pass": 0})
    by_tier: dict[str, dict[str, Any]] = defaultdict(lambda: {"total": 0, "pass": 0})
    by_bucket = Counter()

    for r in records:
        fam = str(r.get("family", "unknown"))
        tier = str(r.get("tier", "unknown"))
        bucket = str(r.get("bucket", "unknown"))
        by_family[fam]["total"] += 1
        by_tier[tier]["total"] += 1
        by_bucket[bucket] += 1
        if bucket == "pass":
            by_family[fam]["pass"] += 1
            by_tier[tier]["pass"] += 1

    return {
        "total": total,
        "test1_rate": _rate(t1, total),
        "test2_rate": _rate(t2, total),
        "combined_rate": _rate(combined, total),
        "pass_at_k": {"k": 1, "combined_rate": _rate(combined, total)},
        "by_family": {
            k: {"total": v["total"], "combined_rate": _rate(v["pass"], v["total"])}
            for k, v in sorted(by_family.items())
        },
        "by_tier": {
            k: {"total": v["total"], "combined_rate": _rate(v["pass"], v["total"])}
            for k, v in sorted(by_tier.items())
        },
        "by_bucket": dict(by_bucket),
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
    lines.append(f"- Total attempts: {summary['total']}")
    lines.append(f"- Test1 rate: {summary['test1_rate']:.3f}")
    lines.append(f"- Test2 rate: {summary['test2_rate']:.3f}")
    lines.append(f"- Combined rate: {summary['combined_rate']:.3f}")
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
        lines.append(f"- item `{row.get('item_id')}` bucket `{row.get('bucket')}`")
        lines.append(f"  - candidate: `{row.get('candidate_raw', '')[:120]}`")
        lines.append(f"  - stderr: `{str(row.get('stderr_excerpt', '')).strip()[:180]}`")
        shown += 1
        if shown >= 10:
            break

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")

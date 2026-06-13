from __future__ import annotations

import json
import re
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

from .dataset import ALLOWED_SPLIT, DatasetError, load_split
from .types import DatasetItem


_WS_RE = re.compile(r"\s+")


def audit_dataset(
    dataset_dir: Path, *, min_per_family_split: int = 0
) -> dict[str, Any]:
    """Compute a dataset-wide benchmark health report.

    The split validator checks row-level Lean and family semantics. This audit
    focuses on benchmark-level evidence: coverage, duplicate/leakage risk,
    provenance diversity, and version drift.
    """
    items_by_split: dict[str, list[DatasetItem]] = {}
    load_errors: list[str] = []
    for split in sorted(ALLOWED_SPLIT):
        try:
            items_by_split[split] = load_split(dataset_dir, split)
        except DatasetError as exc:
            items_by_split[split] = []
            load_errors.append(str(exc))

    all_items = [item for items in items_by_split.values() for item in items]
    ids = [item.id for item in all_items]
    duplicate_ids = sorted(
        [item_id for item_id, count in Counter(ids).items() if count > 1]
    )

    by_split = {
        split: _coverage_for_items(items)
        for split, items in sorted(items_by_split.items())
    }
    by_family = _family_coverage(all_items)
    by_source_kind = dict(
        sorted(Counter(item.provenance.source_kind for item in all_items).items())
    )
    by_license = dict(
        sorted(Counter(item.provenance.license for item in all_items).items())
    )
    schema_versions = dict(
        sorted(Counter(item.schema_version for item in all_items).items())
    )
    checker_versions = dict(
        sorted(Counter(item.checker_version for item in all_items).items())
    )

    duplicate_nl = _duplicate_field_groups(all_items, "nl")
    duplicate_expected = _duplicate_field_groups(all_items, "expected")
    cross_split_duplicate_nl = _cross_split_groups(duplicate_nl)
    cross_split_duplicate_expected = _cross_split_groups(duplicate_expected)
    coverage_gaps = _coverage_gaps(
        items_by_split,
        min_per_family_split=max(0, min_per_family_split),
    )

    issues: list[dict[str, Any]] = []
    for error in load_errors:
        issues.append({"severity": "error", "kind": "load_error", "detail": error})
    for item_id in duplicate_ids:
        issues.append({"severity": "error", "kind": "duplicate_id", "id": item_id})
    for group in cross_split_duplicate_nl:
        issues.append(
            {"severity": "warning", "kind": "cross_split_duplicate_nl", **group}
        )
    for group in cross_split_duplicate_expected:
        issues.append(
            {"severity": "warning", "kind": "cross_split_duplicate_expected", **group}
        )
    for gap in coverage_gaps:
        issues.append({"severity": "warning", "kind": "coverage_gap", **gap})
    if len(schema_versions) > 1:
        issues.append(
            {
                "severity": "warning",
                "kind": "schema_version_drift",
                "versions": schema_versions,
            }
        )
    if len(checker_versions) > 1:
        issues.append(
            {
                "severity": "warning",
                "kind": "checker_version_drift",
                "versions": checker_versions,
            }
        )

    return {
        "dataset_dir": str(dataset_dir),
        "total_items": len(all_items),
        "splits": by_split,
        "families": by_family,
        "source_kinds": by_source_kind,
        "licenses": by_license,
        "schema_versions": schema_versions,
        "checker_versions": checker_versions,
        "duplicate_ids": duplicate_ids,
        "duplicate_nl_groups": duplicate_nl,
        "duplicate_expected_groups": duplicate_expected,
        "cross_split_duplicate_nl": cross_split_duplicate_nl,
        "cross_split_duplicate_expected": cross_split_duplicate_expected,
        "coverage_gaps": coverage_gaps,
        "issues": issues,
        "issue_counts": dict(
            sorted(Counter(issue["kind"] for issue in issues).items())
        ),
    }


def write_audit_json(path: Path, audit: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


def write_audit_markdown(path: Path, audit: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(render_audit_markdown(audit), encoding="utf-8")


def render_audit_markdown(audit: dict[str, Any]) -> str:
    lines: list[str] = [
        "# Autoformalization Dataset Audit",
        "",
        f"- Dataset: `{audit['dataset_dir']}`",
        f"- Total items: `{audit['total_items']}`",
        f"- Issues: `{len(audit['issues'])}`",
        "",
        "## Split Coverage",
        "",
        "| Split | Items | Families | Tier A | Tier B |",
        "|---|---:|---:|---:|---:|",
    ]
    for split, stats in audit["splits"].items():
        lines.append(
            f"| {split} | {stats['count']} | {len(stats['families'])} | "
            f"{stats['tiers'].get('A', 0)} | {stats['tiers'].get('B', 0)} |"
        )

    lines.extend(
        [
            "",
            "## Family Coverage",
            "",
            "| Family | Items | Splits | Tier A | Tier B |",
            "|---|---:|---|---:|---:|",
        ]
    )
    for family, stats in audit["families"].items():
        lines.append(
            f"| {family} | {stats['count']} | {', '.join(stats['splits'])} | "
            f"{stats['tiers'].get('A', 0)} | {stats['tiers'].get('B', 0)} |"
        )

    lines.extend(["", "## Provenance", "", "| Source kind | Items |", "|---|---:|"])
    for source_kind, count in audit["source_kinds"].items():
        lines.append(f"| {source_kind} | {count} |")

    lines.extend(["", "## Issues", ""])
    if not audit["issues"]:
        lines.append("No benchmark-level issues detected.")
    else:
        lines.append("| Severity | Kind | Detail |")
        lines.append("|---|---|---|")
        for issue in audit["issues"]:
            detail = _issue_detail(issue)
            lines.append(f"| {issue['severity']} | {issue['kind']} | {detail} |")
    return "\n".join(lines) + "\n"


def _coverage_for_items(items: list[DatasetItem]) -> dict[str, Any]:
    family_counts = Counter(item.family for item in items)
    tier_counts = Counter(item.tier for item in items)
    check_counts = Counter(item.semantic.check for item in items)
    source_counts = Counter(item.provenance.source_kind for item in items)
    return {
        "count": len(items),
        "families": dict(sorted(family_counts.items())),
        "tiers": dict(sorted(tier_counts.items())),
        "checks": dict(sorted(check_counts.items())),
        "source_kinds": dict(sorted(source_counts.items())),
    }


def _family_coverage(items: list[DatasetItem]) -> dict[str, dict[str, Any]]:
    grouped: dict[str, list[DatasetItem]] = defaultdict(list)
    for item in items:
        grouped[item.family].append(item)
    return {
        family: {
            "count": len(rows),
            "splits": sorted({row.split for row in rows}),
            "tiers": dict(sorted(Counter(row.tier for row in rows).items())),
            "checks": dict(sorted(Counter(row.semantic.check for row in rows).items())),
        }
        for family, rows in sorted(grouped.items())
    }


def _duplicate_field_groups(
    items: list[DatasetItem], field: str
) -> list[dict[str, Any]]:
    grouped: dict[str, list[DatasetItem]] = defaultdict(list)
    for item in items:
        value = getattr(item, field)
        if not isinstance(value, str):
            continue
        key = _normalize_text(value)
        if key:
            grouped[key].append(item)

    duplicates: list[dict[str, Any]] = []
    for key, rows in sorted(grouped.items()):
        if len(rows) <= 1:
            continue
        duplicates.append(
            {
                "normalized": key,
                "items": [
                    {"id": row.id, "split": row.split, "family": row.family}
                    for row in sorted(rows, key=lambda item: (item.split, item.id))
                ],
            }
        )
    return duplicates


def _cross_split_groups(groups: list[dict[str, Any]]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for group in groups:
        splits = sorted({item["split"] for item in group["items"]})
        if len(splits) <= 1:
            continue
        out.append(
            {
                "normalized": group["normalized"],
                "splits": splits,
                "items": group["items"],
            }
        )
    return out


def _coverage_gaps(
    items_by_split: dict[str, list[DatasetItem]], *, min_per_family_split: int
) -> list[dict[str, Any]]:
    if min_per_family_split <= 0:
        return []
    families = sorted(
        {item.family for items in items_by_split.values() for item in items}
    )
    gaps: list[dict[str, Any]] = []
    for split, items in sorted(items_by_split.items()):
        counts = Counter(item.family for item in items)
        for family in families:
            count = counts.get(family, 0)
            if count < min_per_family_split:
                gaps.append(
                    {
                        "split": split,
                        "family": family,
                        "count": count,
                        "minimum": min_per_family_split,
                    }
                )
    return gaps


def _normalize_text(value: str) -> str:
    return _WS_RE.sub(" ", value.strip()).lower()


def _issue_detail(issue: dict[str, Any]) -> str:
    if "detail" in issue:
        return str(issue["detail"])
    if "id" in issue:
        return f"id={issue['id']}"
    if issue["kind"] == "coverage_gap":
        return (
            f"{issue['split']} / {issue['family']}: "
            f"{issue['count']} < {issue['minimum']}"
        )
    if "splits" in issue:
        ids = ", ".join(f"{item['split']}:{item['id']}" for item in issue["items"])
        return f"splits={','.join(issue['splits'])}; items={ids}"
    if "versions" in issue:
        return json.dumps(issue["versions"], sort_keys=True)
    return ""

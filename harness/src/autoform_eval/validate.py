from __future__ import annotations

import json
from dataclasses import asdict
from pathlib import Path
from typing import Any

from .dataset import load_split
from .lean_runner import classify_failure, run_lean_file
from .mutate import generate_mutants
from .parse import has_forbidden_tokens
from .render import render_test1, render_test2
from .types import DatasetItem


FORBIDDEN_DATASET_TOKENS = {
    "theorem",
    "lemma",
    "def",
    "example",
    "namespace",
    "section",
    "sorry",
}


def _dataset_forbidden_issues(item: DatasetItem) -> list[str]:
    issues: list[str] = []
    allow = set(item.forbidden_ok)
    for field_name, text in (
        ("context", item.context),
        ("expected", item.expected),
        ("semantic.extra", item.semantic.extra or ""),
    ):
        bad = has_forbidden_tokens(text, forbidden_ok=allow | {"by"}, strict_reject_assign=False)
        if bad and bad in FORBIDDEN_DATASET_TOKENS:
            issues.append(f"forbidden_token:{field_name}:{bad}")
    return issues


def _write_rendered(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _self_check(
    item: DatasetItem,
    lean_dir: Path,
    work_dir: Path,
    test1_heartbeats: int,
    test2_heartbeats: int,
    timeout1_s: float,
    timeout2_s: float,
) -> tuple[bool, list[str], dict[str, int]]:
    reasons: list[str] = []
    timings: dict[str, int] = {}

    t1_content = render_test1(lean_dir, item, item.expected, test1_heartbeats)
    t1_path = work_dir / f"{item.id}.self.test1.lean"
    _write_rendered(t1_path, t1_content)
    r1 = run_lean_file(lean_dir, t1_path, timeout1_s)
    timings["self_test1_elapsed_ms"] = r1.elapsed_ms
    if not r1.ok:
        reasons.append(f"self_test1:{classify_failure(r1.stderr, r1.timed_out)}")
        return False, reasons, timings

    t2_content = render_test2(lean_dir, item, item.expected, test2_heartbeats)
    t2_path = work_dir / f"{item.id}.self.test2.lean"
    _write_rendered(t2_path, t2_content)
    r2 = run_lean_file(lean_dir, t2_path, timeout2_s)
    timings["self_test2_elapsed_ms"] = r2.elapsed_ms
    if not r2.ok:
        reasons.append(f"self_test2:{classify_failure(r2.stderr, r2.timed_out)}")
        return False, reasons, timings

    return True, reasons, timings


def _mutation_check(
    item: DatasetItem,
    lean_dir: Path,
    work_dir: Path,
    test1_heartbeats: int,
    test2_heartbeats: int,
    timeout1_s: float,
    timeout2_s: float,
) -> tuple[bool, list[str], dict[str, int]]:
    reasons: list[str] = []
    timings: dict[str, int] = {}
    mutants = generate_mutants(item)
    if not mutants:
        reasons.append("mutation:none_generated")
        return False, reasons, timings

    rejected = 0
    for idx, cand in enumerate(mutants, 1):
        t1_content = render_test1(lean_dir, item, cand, test1_heartbeats)
        t1_path = work_dir / f"{item.id}.mut{idx}.test1.lean"
        _write_rendered(t1_path, t1_content)
        r1 = run_lean_file(lean_dir, t1_path, timeout1_s)
        timings[f"mut{idx}_test1_elapsed_ms"] = r1.elapsed_ms
        if not r1.ok:
            rejected += 1
            continue

        t2_content = render_test2(lean_dir, item, cand, test2_heartbeats)
        t2_path = work_dir / f"{item.id}.mut{idx}.test2.lean"
        _write_rendered(t2_path, t2_content)
        r2 = run_lean_file(lean_dir, t2_path, timeout2_s)
        timings[f"mut{idx}_test2_elapsed_ms"] = r2.elapsed_ms
        if not r2.ok:
            rejected += 1

    if rejected == 0:
        reasons.append("mutation:all_mutants_passed")
        return False, reasons, timings

    return True, reasons, timings


def validate_split(
    dataset_dir: Path,
    split: str,
    lean_dir: Path,
    out_report: Path,
    rendered_dir: Path,
    use_lean: bool,
    test1_heartbeats: int,
    test2_heartbeats: int,
    timeout1_s: float,
    timeout2_s: float,
) -> dict[str, Any]:
    items = load_split(dataset_dir, split)
    results: list[dict[str, Any]] = []

    for item in items:
        entry: dict[str, Any] = {
            "item_id": item.id,
            "split": item.split,
            "family": item.family,
            "tier": item.tier,
            "valid": True,
            "issues": [],
            "timings_ms": {},
        }

        issues = _dataset_forbidden_issues(item)
        if issues:
            entry["valid"] = False
            entry["issues"].extend(issues)

        if use_lean:
            ok_self, reasons_self, timings_self = _self_check(
                item,
                lean_dir=lean_dir,
                work_dir=rendered_dir,
                test1_heartbeats=test1_heartbeats,
                test2_heartbeats=test2_heartbeats,
                timeout1_s=timeout1_s,
                timeout2_s=timeout2_s,
            )
            entry["timings_ms"].update(timings_self)
            if not ok_self:
                entry["valid"] = False
                entry["issues"].extend(reasons_self)

            ok_mut, reasons_mut, timings_mut = _mutation_check(
                item,
                lean_dir=lean_dir,
                work_dir=rendered_dir,
                test1_heartbeats=test1_heartbeats,
                test2_heartbeats=test2_heartbeats,
                timeout1_s=timeout1_s,
                timeout2_s=timeout2_s,
            )
            entry["timings_ms"].update(timings_mut)
            if not ok_mut:
                entry["valid"] = False
                entry["issues"].extend(reasons_mut)

        results.append(entry)

    summary = {
        "split": split,
        "total": len(results),
        "valid": sum(1 for r in results if r["valid"]),
        "invalid": sum(1 for r in results if not r["valid"]),
        "items": results,
    }

    out_report.parent.mkdir(parents=True, exist_ok=True)
    out_report.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return summary

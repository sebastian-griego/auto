from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from .dataset import iter_all_splits, load_split
from .lean_runner import classify_failure, run_lean_file
from .mutate import generate_mutants
from .prompt import BENCHMARK_PROMPT_VERSION
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
WS_RE = re.compile(r"\s+")
LEADING_FORALL_RE = re.compile(r"^\s*(?:\u2200|forall)\s+([^:]+?)\s*:\s*([^,]+?)\s*,\s*(.*)$", re.DOTALL)
FIN_TYPE_RE = re.compile(r"^Fin\s*\(?\s*(\d+)\s*\)?$")
INDUCTIVE_RE = re.compile(r"^inductive\s+([A-Za-z_][A-Za-z0-9_']*)\b")
BOOL_CONNECTIVES = ("&&", "||")


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


def _extract_enum_cap(tags: list[str]) -> int | None:
    for tag in tags:
        if not tag.startswith("enum_cap:"):
            continue
        value = tag.split(":", 1)[1].strip()
        if not value.isdigit():
            return -1
        return int(value)
    return None


def _dataset_family_issues(item: DatasetItem) -> list[str]:
    issues: list[str] = []
    if item.family == "fin_truth_table":
        enum_cap = _extract_enum_cap(item.tags)
        if enum_cap is None:
            issues.append("missing_tag:enum_cap")
        elif enum_cap < 0:
            issues.append("invalid_tag:enum_cap")
        elif enum_cap > 256:
            issues.append(f"enum_cap_exceeded:{enum_cap}>256")
        else:
            computed_cap, reason = _compute_enum_cap_from_item(item)
            if reason is not None:
                issues.append(f"enum_cap_compute_error:{reason}")
            elif computed_cap is None:
                issues.append("enum_cap_compute_error:no_finite_prefix")
            elif computed_cap != enum_cap:
                issues.append(f"enum_cap_mismatch:tag={enum_cap}:computed={computed_cap}")

        bool_eq_paren_issue = _fin_truth_table_bool_eq_parentheses_issue(item.expected)
        if bool_eq_paren_issue is not None:
            issues.append(bool_eq_paren_issue)
    return issues


def _strip_leading_foralls(expr: str) -> str:
    body = expr.strip()
    while True:
        match = LEADING_FORALL_RE.match(body)
        if not match:
            break
        body = match.group(3).strip()
    return body


def _split_top_level_eq(expr: str) -> tuple[str, str] | None:
    depth = 0
    for idx, ch in enumerate(expr):
        if ch == "(":
            depth += 1
            continue
        if ch == ")":
            if depth > 0:
                depth -= 1
            continue
        if ch != "=" or depth != 0:
            continue
        prev = expr[idx - 1] if idx > 0 else ""
        nxt = expr[idx + 1] if idx + 1 < len(expr) else ""
        if prev in {":", "<", ">", "!"} or nxt == ">":
            continue
        lhs = expr[:idx].strip()
        rhs = expr[idx + 1 :].strip()
        if lhs and rhs:
            return lhs, rhs
        return None
    return None


def _contains_top_level_bool_connective(expr: str) -> bool:
    depth = 0
    idx = 0
    while idx < len(expr):
        ch = expr[idx]
        if ch == "(":
            depth += 1
            idx += 1
            continue
        if ch == ")":
            if depth > 0:
                depth -= 1
            idx += 1
            continue
        if depth == 0 and idx + 1 < len(expr) and expr[idx : idx + 2] in BOOL_CONNECTIVES:
            return True
        idx += 1
    return False


def _fin_truth_table_bool_eq_parentheses_issue(expected: str) -> str | None:
    body = _strip_leading_foralls(expected)
    split = _split_top_level_eq(body)
    if split is None:
        return None
    lhs, rhs = split
    if _contains_top_level_bool_connective(lhs):
        return "fin_truth_table_bool_eq_parentheses:lhs"
    if _contains_top_level_bool_connective(rhs):
        return "fin_truth_table_bool_eq_parentheses:rhs"
    return None


def _parse_context_enum_sizes(context: str) -> dict[str, int]:
    enum_sizes: dict[str, int] = {}
    current_name: str | None = None
    current_ctors = 0
    for raw_line in context.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        match = INDUCTIVE_RE.match(line)
        if match:
            if current_name is not None and current_ctors > 0:
                enum_sizes[current_name] = current_ctors
            current_name = match.group(1)
            current_ctors = 0
            continue
        if current_name is None:
            continue
        if line.startswith("|"):
            current_ctors += 1
            continue
        if line.startswith("deriving"):
            if current_ctors > 0:
                enum_sizes[current_name] = current_ctors
            current_name = None
            current_ctors = 0
            continue
        if current_ctors > 0:
            enum_sizes[current_name] = current_ctors
        current_name = None
        current_ctors = 0
    if current_name is not None and current_ctors > 0:
        enum_sizes[current_name] = current_ctors
    return enum_sizes


def _finite_domain_size(ty: str, enum_sizes: dict[str, int]) -> int | None:
    ty_norm = ty.strip()
    if ty_norm == "Bool":
        return 2
    fin_match = FIN_TYPE_RE.match(ty_norm)
    if fin_match:
        return int(fin_match.group(1))
    if ty_norm in enum_sizes:
        return enum_sizes[ty_norm]
    return None


def _compute_enum_cap_from_item(item: DatasetItem) -> tuple[int | None, str | None]:
    expected = item.expected.strip()
    enum_sizes = _parse_context_enum_sizes(item.context)
    cap = 1
    saw_finite_binder = False

    while True:
        match = LEADING_FORALL_RE.match(expected)
        if not match:
            break
        vars_part = match.group(1).strip()
        ty_part = match.group(2).strip()
        expected = match.group(3).strip()

        var_names = [v for v in vars_part.split() if v]
        if not var_names:
            return None, "binder_parse"

        domain_size = _finite_domain_size(ty_part, enum_sizes)
        if domain_size is None:
            break

        saw_finite_binder = True
        for _ in var_names:
            cap *= domain_size

    if not saw_finite_binder:
        return None, None
    return cap, None


def _normalize_text(value: str) -> str:
    return WS_RE.sub(" ", value.strip())


def _build_cross_split_indexes(
    dataset_dir: Path,
    split: str,
) -> tuple[dict[str, list[tuple[str, str]]], dict[str, list[tuple[str, str]]]]:
    other_split_nl: dict[str, list[tuple[str, str]]] = {}
    other_split_expected: dict[str, list[tuple[str, str]]] = {}
    for other_split, items in iter_all_splits(dataset_dir):
        if other_split == split:
            continue
        for item in items:
            nl_key = _normalize_text(item.nl)
            expected_key = _normalize_text(item.expected)
            if nl_key:
                other_split_nl.setdefault(nl_key, []).append((other_split, item.id))
            if expected_key:
                other_split_expected.setdefault(expected_key, []).append((other_split, item.id))
    return other_split_nl, other_split_expected


def _write_rendered(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _warmup_lean(lean_dir: Path, work_dir: Path, timeout_s: float) -> None:
    # Prime toolchain/import startup so timed per-item checks are not skewed by first-run overhead.
    warmup_content = "\n".join(
        [
            "import Mathlib",
            "import AutoformalizationEval.Checks",
            "set_option autoImplicit false",
            "def _autoform_eval_warmup : Prop := True",
        ]
    )
    warmup_path = work_dir / "_validate_warmup.lean"
    _write_rendered(warmup_path, warmup_content)
    run_lean_file(lean_dir, warmup_path, timeout_s)


def _enforce_time_budget(
    timings_ms: dict[str, int],
    budget1_ms: int | None,
    budget2_ms: int | None,
) -> list[str]:
    issues: list[str] = []
    for key, elapsed in timings_ms.items():
        if key.endswith("test1_elapsed_ms") and budget1_ms is not None and elapsed > budget1_ms:
            issues.append(f"budget_exceeded:{key}:{elapsed}>{budget1_ms}")
        if key.endswith("test2_elapsed_ms") and budget2_ms is not None and elapsed > budget2_ms:
            issues.append(f"budget_exceeded:{key}:{elapsed}>{budget2_ms}")
    return issues


def _self_check(
    item: DatasetItem,
    lean_dir: Path,
    work_dir: Path,
    test1_heartbeats: int,
    test2_heartbeats: int,
    timeout1_s: float,
    timeout2_s: float,
    prompt_version: str,
) -> tuple[bool, list[str], dict[str, int]]:
    reasons: list[str] = []
    timings: dict[str, int] = {}

    t1_content = render_test1(lean_dir, item, item.expected, test1_heartbeats)
    t1_path = work_dir / f"{item.id}.self.test1.lean"
    _write_rendered(t1_path, t1_content)
    r1 = run_lean_file(lean_dir, t1_path, timeout1_s)
    timings["self_test1_elapsed_ms"] = r1.elapsed_ms
    if not r1.ok:
        reasons.append(f"self_test1:{classify_failure(r1.stderr, r1.timed_out, r1.stdout)}")
        return False, reasons, timings

    t2_content = render_test2(
        lean_dir,
        item,
        item.expected,
        test2_heartbeats,
        prompt_version=prompt_version,
    )
    t2_path = work_dir / f"{item.id}.self.test2.lean"
    _write_rendered(t2_path, t2_content)
    r2 = run_lean_file(lean_dir, t2_path, timeout2_s)
    timings["self_test2_elapsed_ms"] = r2.elapsed_ms
    if not r2.ok:
        reasons.append(f"self_test2:{classify_failure(r2.stderr, r2.timed_out, r2.stdout)}")
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
    prompt_version: str,
) -> tuple[bool, list[str], dict[str, int]]:
    reasons: list[str] = []
    timings: dict[str, int] = {}
    mutants = generate_mutants(item)
    if not mutants:
        reasons.append("mutation:none_generated")
        return False, reasons, timings

    elaborating_mutants = 0
    shape_or_semantic_rejects = 0
    for idx, cand in enumerate(mutants, 1):
        t1_content = render_test1(lean_dir, item, cand, test1_heartbeats)
        t1_path = work_dir / f"{item.id}.mut{idx}.test1.lean"
        _write_rendered(t1_path, t1_content)
        r1 = run_lean_file(lean_dir, t1_path, timeout1_s)
        timings[f"mut{idx}_test1_elapsed_ms"] = r1.elapsed_ms
        if not r1.ok:
            continue

        elaborating_mutants += 1
        t2_content = render_test2(
            lean_dir,
            item,
            cand,
            test2_heartbeats,
            prompt_version=prompt_version,
        )
        t2_path = work_dir / f"{item.id}.mut{idx}.test2.lean"
        _write_rendered(t2_path, t2_content)
        r2 = run_lean_file(lean_dir, t2_path, timeout2_s)
        timings[f"mut{idx}_test2_elapsed_ms"] = r2.elapsed_ms
        if not r2.ok:
            bucket = classify_failure(r2.stderr, r2.timed_out, r2.stdout)
            if bucket in {"shape_fail", "semantic_fail"}:
                shape_or_semantic_rejects += 1

    if elaborating_mutants == 0:
        reasons.append("mutation:no_elaborating_mutant")
        return False, reasons, timings

    if shape_or_semantic_rejects == 0:
        reasons.append("mutation:no_shape_or_semantic_reject")
        return False, reasons, timings

    return True, reasons, timings


def _determinism_check(
    item: DatasetItem,
    lean_dir: Path,
    work_dir: Path,
    test2_heartbeats: int,
    timeout2_s: float,
    repeats: int,
    jitter_ms: int | None,
    prompt_version: str,
) -> tuple[bool, list[str], dict[str, int]]:
    reasons: list[str] = []
    timings: dict[str, int] = {}
    if repeats <= 1:
        return True, reasons, timings

    outcomes: list[tuple[bool, str]] = []
    elapsed_values: list[int] = []
    for idx in range(1, repeats + 1):
        t2_content = render_test2(
            lean_dir,
            item,
            item.expected,
            test2_heartbeats,
            prompt_version=prompt_version,
        )
        t2_path = work_dir / f"{item.id}.det{idx}.test2.lean"
        _write_rendered(t2_path, t2_content)
        r2 = run_lean_file(lean_dir, t2_path, timeout2_s)
        timings[f"det{idx}_test2_elapsed_ms"] = r2.elapsed_ms

        bucket = "pass" if r2.ok else classify_failure(r2.stderr, r2.timed_out, r2.stdout)
        outcomes.append((r2.ok, bucket))
        elapsed_values.append(r2.elapsed_ms)
        if not r2.ok:
            reasons.append(f"determinism:repeat{idx}:{bucket}")

    if outcomes:
        baseline = outcomes[0]
        for idx, outcome in enumerate(outcomes[1:], 2):
            if outcome != baseline:
                reasons.append(f"determinism:outcome_mismatch:repeat{idx}")

    if jitter_ms is not None and len(elapsed_values) >= 2:
        jitter = max(elapsed_values) - min(elapsed_values)
        if jitter > jitter_ms:
            reasons.append(f"determinism:jitter_exceeded:{jitter}>{jitter_ms}")

    return len(reasons) == 0, reasons, timings


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
    budget1_ms: int | None,
    budget2_ms: int | None,
    determinism_repeats: int,
    determinism_jitter_ms: int | None,
    prompt_version: str = BENCHMARK_PROMPT_VERSION,
) -> dict[str, Any]:
    items = load_split(dataset_dir, split)
    results: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    seen_nl: dict[str, str] = {}
    seen_expected: dict[str, str] = {}
    other_split_nl, other_split_expected = _build_cross_split_indexes(dataset_dir, split)

    if use_lean:
        _warmup_lean(
            lean_dir=lean_dir,
            work_dir=rendered_dir,
            timeout_s=max(timeout1_s, timeout2_s, 30.0),
        )

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

        if item.id in seen_ids:
            entry["valid"] = False
            entry["issues"].append(f"duplicate_id:{item.id}")
        else:
            seen_ids.add(item.id)

        nl_key = _normalize_text(item.nl)
        if nl_key:
            prior_nl = seen_nl.get(nl_key)
            if prior_nl:
                entry["valid"] = False
                entry["issues"].append(f"duplicate_nl:{prior_nl}")
            else:
                seen_nl[nl_key] = item.id

            other_nl_matches = other_split_nl.get(nl_key, [])
            if other_nl_matches:
                entry["valid"] = False
                for other_split, other_id in other_nl_matches:
                    entry["issues"].append(f"cross_split_duplicate_nl:{other_split}:{other_id}")

        expected_key = _normalize_text(item.expected)
        if expected_key:
            prior_expected = seen_expected.get(expected_key)
            if prior_expected:
                entry["valid"] = False
                entry["issues"].append(f"duplicate_expected:{prior_expected}")
            else:
                seen_expected[expected_key] = item.id

            other_expected_matches = other_split_expected.get(expected_key, [])
            if other_expected_matches:
                entry["valid"] = False
                for other_split, other_id in other_expected_matches:
                    entry["issues"].append(f"cross_split_duplicate_expected:{other_split}:{other_id}")

        if item.split != split:
            entry["valid"] = False
            entry["issues"].append(f"split_mismatch:{item.split}!={split}")

        issues = _dataset_forbidden_issues(item)
        issues.extend(_dataset_family_issues(item))
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
                prompt_version=prompt_version,
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
                prompt_version=prompt_version,
            )
            entry["timings_ms"].update(timings_mut)
            if not ok_mut:
                entry["valid"] = False
                entry["issues"].extend(reasons_mut)

            ok_det, reasons_det, timings_det = _determinism_check(
                item,
                lean_dir=lean_dir,
                work_dir=rendered_dir,
                test2_heartbeats=test2_heartbeats,
                timeout2_s=timeout2_s,
                repeats=determinism_repeats,
                jitter_ms=determinism_jitter_ms,
                prompt_version=prompt_version,
            )
            entry["timings_ms"].update(timings_det)
            if not ok_det:
                entry["valid"] = False
                entry["issues"].extend(reasons_det)

            budget_issues = _enforce_time_budget(
                entry["timings_ms"],
                budget1_ms=budget1_ms,
                budget2_ms=budget2_ms,
            )
            if budget_issues:
                entry["valid"] = False
                entry["issues"].extend(budget_issues)

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

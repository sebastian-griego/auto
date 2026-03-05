from __future__ import annotations

import re

from .types import DatasetItem

LEADING_FORALL_RE = re.compile(r"^\s*(?:\u2200|forall)\s+([^:]+?)\s*:\s*([^,]+?)\s*,\s*(.*)$", re.DOTALL)


def _replace_first(text: str, old: str, new: str) -> str | None:
    if old not in text:
        return None
    return text.replace(old, new, 1)


def _mutate_ring(expr: str) -> list[str]:
    muts: list[str] = []
    m = _replace_first(expr, "+", "*")
    if m:
        muts.append(m)
    m = _replace_first(expr, "*", "+")
    if m:
        muts.append(m)
    if " = " in expr:
        if "∀" in expr and "," in expr:
            prefix, body = expr.split(",", 1)
            if " = " in body:
                left, right = body.split(" = ", 1)
                muts.append(f"{prefix}, {right.strip()} = {left.strip()}")
        else:
            left, right = expr.split(" = ", 1)
            muts.append(f"{right} = {left}")
    num_match = re.search(r"\b(\d+)\b", expr)
    if num_match:
        start, end = num_match.span(1)
        value = int(num_match.group(1))
        muts.append(f"{expr[:start]}{value + 1}{expr[end:]}")
    return muts


def _mutate_fin_truth_table(expr: str) -> list[str]:
    muts: list[str] = []
    m = _replace_first(expr, "∀", "∃")
    if m:
        muts.append(m)
    m = _replace_first(expr, "∃", "∀")
    if m:
        muts.append(m)
    m = _replace_first(expr, "forall", "exists")
    if m:
        muts.append(m)
    m = _replace_first(expr, "exists", "forall")
    if m:
        muts.append(m)
    m = _replace_first(expr, "= true", "= false")
    if m:
        muts.append(m)
    m = _replace_first(expr, "= false", "= true")
    if m:
        muts.append(m)
    m = _replace_first(expr, "∧", "∨")
    if m:
        muts.append(m)
    m = _replace_first(expr, "∨", "∧")
    if m:
        muts.append(m)
    m = _replace_first(expr, "->", "∧")
    if m:
        muts.append(m)
    muts.append(f"¬({expr})")
    return muts


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


def _split_forall_prefix(expr: str) -> tuple[str, str]:
    rest = expr.strip()
    prefixes: list[str] = []
    while True:
        match = LEADING_FORALL_RE.match(rest)
        if not match:
            break
        vars_part = match.group(1).strip()
        ty_part = match.group(2).strip()
        prefixes.append(f"∀ {vars_part} : {ty_part},")
        rest = match.group(3).strip()
    if not prefixes:
        return "", rest
    return f"{' '.join(prefixes)} ", rest


def _insert_complement_once(expr: str) -> str | None:
    prefix, body = _split_forall_prefix(expr)
    split = _split_top_level_eq(body)
    if split is None:
        return None
    lhs, rhs = split
    return f"{prefix}({lhs})ᶜ = {rhs}"


def _mutate_set_equality(expr: str) -> list[str]:
    muts: list[str] = []

    if "ᶜ" in expr:
        muts.append(expr.replace("ᶜ", "", 1))
    elif "Set.compl " in expr:
        muts.append(expr.replace("Set.compl ", "", 1))
    else:
        m = _insert_complement_once(expr)
        if m:
            muts.append(m)

    m = _replace_first(expr, "\\", "∩")
    if m:
        muts.append(m)
    m = _replace_first(expr, "∩", "\\")
    if m:
        muts.append(m)

    for old, new in (
        ("∪", "∩"),
        ("∩", "∪"),
        ("Set.union", "Set.inter"),
        ("Set.inter", "Set.union"),
        ("Set.univ", "∅"),
        ("∅", "Set.univ"),
    ):
        m = _replace_first(expr, old, new)
        if m:
            muts.append(m)

    # Flip a small numeral in equality predicates (e.g. `x = 0` -> `x = 1`).
    num_eq = re.search(r"=\s*(\d+)\b", expr)
    if num_eq:
        start, end = num_eq.span(1)
        value = int(num_eq.group(1))
        replacement = 1 if value == 0 else 0
        muts.append(f"{expr[:start]}{replacement}{expr[end:]}")

    return muts


def generate_mutants(item: DatasetItem, max_mutants: int = 3) -> list[str]:
    expected = item.expected
    if item.family == "ring_identity":
        muts = _mutate_ring(expected)
    elif item.family == "fin_truth_table":
        muts = _mutate_fin_truth_table(expected)
    elif item.family == "set_equality":
        muts = _mutate_set_equality(expected)
    else:
        muts = [f"¬({expected})"]

    out: list[str] = []
    seen: set[str] = set()
    for m in muts:
        m = m.strip()
        if m and m != expected and m not in seen:
            out.append(m)
            seen.add(m)
        if len(out) >= max_mutants:
            break
    return out

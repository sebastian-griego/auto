from __future__ import annotations

import re

from .types import DatasetItem


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
    m = _replace_first(expr, "= true", "= false")
    if m:
        muts.append(m)
    m = _replace_first(expr, "= false", "= true")
    if m:
        muts.append(m)
    m = _replace_first(expr, "->", "∧")
    if m:
        muts.append(m)
    m = _replace_first(expr, "∧", "∨")
    if m:
        muts.append(m)
    muts.append(f"¬({expr})")
    return muts


def generate_mutants(item: DatasetItem, max_mutants: int = 3) -> list[str]:
    expected = item.expected
    if item.family == "ring_identity":
        muts = _mutate_ring(expected)
    elif item.family == "fin_truth_table":
        muts = _mutate_fin_truth_table(expected)
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

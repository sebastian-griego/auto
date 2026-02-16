from __future__ import annotations

from .types import DatasetItem


def _mutate_ring(expr: str) -> list[str]:
    muts: list[str] = []
    if "+" in expr:
        muts.append(expr.replace("+", "*", 1))
    if " = " in expr:
        left, right = expr.split(" = ", 1)
        muts.append(f"{right} = {left}")
    return muts


def _mutate_fin_truth_table(expr: str) -> list[str]:
    muts: list[str] = []
    if "= true" in expr:
        muts.append(expr.replace("= true", "= false", 1))
    if "->" in expr:
        muts.append(expr.replace("->", "∧", 1))
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
    for m in muts:
        m = m.strip()
        if m and m != expected:
            out.append(m)
        if len(out) >= max_mutants:
            break
    return out

from __future__ import annotations

from .types import DatasetItem


BENCHMARK_PROMPT_VERSION = "v1.0.0"

_FRAGMENT_BY_CHECK_KEY = {
    "ring_identity_norm": "ring_identity_norm_v1",
    "fin_truth_table": "fin_truth_table_v1",
    "set_equality_norm": "set_equality_norm_v0",
}

_FAMILY_FRAGMENT_RULES = {
    "ring_identity": (
        "Fragment ring_identity_norm_v1: use only forall binders, equality (=), natural numerals, "
        "(+), (*), and parentheses."
    ),
    "fin_truth_table": (
        "Fragment fin_truth_table_v1: use propositions over finite leading binders "
        "(Bool, concrete Fin n, or small nullary enums from context) with logical connectives/equalities."
    ),
    "set_equality": (
        "Fragment set_equality_norm_v0: use set equality statements only."
    ),
}


def fragment_for_item(item: DatasetItem) -> str:
    for tag in item.tags:
        if not tag.startswith("fragment:"):
            continue
        fragment = tag.split(":", 1)[1].strip()
        if fragment:
            return fragment
    return _FRAGMENT_BY_CHECK_KEY.get(item.semantic.check, f"{item.semantic.check}_v1")


def build_prompt(item: DatasetItem, prompt_version: str = BENCHMARK_PROMPT_VERSION) -> str:
    if prompt_version != BENCHMARK_PROMPT_VERSION:
        raise ValueError(
            f"unsupported prompt version '{prompt_version}' (supported: {BENCHMARK_PROMPT_VERSION})"
        )

    fragment_key = fragment_for_item(item)
    family_rules = _FAMILY_FRAGMENT_RULES.get(item.family, "Stay inside the declared family fragment.")

    parts = [
        f"Benchmark prompt version: {prompt_version}",
        "Return exactly one Lean term that elaborates to Prop.",
        "Introduce all quantified variables explicitly with `forall` unless they are already in Lean context.",
        "Do not return theorem/lemma/def/example/namespace/section/by/sorry.",
        "Do not include markdown fences or commentary.",
        f"Family: {item.family}",
        f"Semantic check key: {item.semantic.check}",
        f"Required fragment key: {fragment_key}",
        family_rules,
        "",
        f"Natural language statement:\n{item.nl.strip()}",
    ]

    context = item.context.strip()
    if context:
        parts.extend(["", f"Lean context:\n{context}"])
    else:
        parts.extend(["", "Lean context:\n(none)"])

    return "\n".join(parts)

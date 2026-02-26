from __future__ import annotations

from .types import DatasetItem


SUPPORTED_PROMPT_VERSIONS = ("v1.0.0", "v1.1.0")
BENCHMARK_PROMPT_VERSION = "v1.1.0"

_FRAGMENT_BY_CHECK_KEY_BY_PROMPT = {
    "v1.0.0": {
        "ring_identity_norm": "ring_identity_norm_v1",
        "fin_truth_table": "fin_truth_table_v1",
        "set_equality_norm": "set_equality_norm_v0",
    },
    "v1.1.0": {
        "ring_identity_norm": "ring_identity_norm_v2",
        "fin_truth_table": "fin_truth_table_v1",
        "set_equality_norm": "set_equality_norm_v0",
    },
}


def is_supported_prompt_version(prompt_version: str) -> bool:
    return prompt_version in SUPPORTED_PROMPT_VERSIONS


def _fragment_map_for_prompt(prompt_version: str) -> dict[str, str]:
    if not is_supported_prompt_version(prompt_version):
        supported = ", ".join(SUPPORTED_PROMPT_VERSIONS)
        raise ValueError(f"unsupported prompt version '{prompt_version}' (supported: {supported})")
    return _FRAGMENT_BY_CHECK_KEY_BY_PROMPT[prompt_version]


def fragment_for_item(item: DatasetItem, prompt_version: str = BENCHMARK_PROMPT_VERSION) -> str:
    for tag in item.tags:
        if not tag.startswith("fragment:"):
            continue
        fragment = tag.split(":", 1)[1].strip()
        if fragment:
            return fragment
    return _fragment_map_for_prompt(prompt_version).get(item.semantic.check, f"{item.semantic.check}_v1")


def _family_rules(item: DatasetItem, fragment_key: str) -> str:
    if item.family == "ring_identity":
        return (
            f"Fragment {fragment_key}: use only forall binders, equality (=), natural numerals, "
            "(+), (*), and parentheses."
        )
    if item.family == "fin_truth_table":
        return (
            f"Fragment {fragment_key}: use propositions over finite leading binders "
            "(Bool, concrete Fin n, or small nullary enums from context) with logical connectives/equalities. "
            "When using Bool connectives (`&&` or `||`) inside equality, parenthesize them: write "
            "`(a && b) = false` or `(a || b) = false`, not `a && b = false` or `a || b = false`."
        )
    if item.family == "set_equality":
        return f"Fragment {fragment_key}: use set equality statements only."
    return "Stay inside the declared family fragment."


def build_prompt(item: DatasetItem, prompt_version: str = BENCHMARK_PROMPT_VERSION) -> str:
    fragment_key = fragment_for_item(item, prompt_version=prompt_version)
    family_rules = _family_rules(item, fragment_key)

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

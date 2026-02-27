from __future__ import annotations

from pathlib import Path

from .prompt import BENCHMARK_PROMPT_VERSION, fragment_for_item
from .types import DatasetItem


def _template_path(lean_dir: Path, name: str) -> Path:
    return lean_dir / "AutoformalizationEval" / "Template" / name


def render_imports(imports: list[str]) -> str:
    lines = []
    for imp in imports:
        imp = imp.strip()
        if not imp:
            continue
        lines.append(f"import {imp}")
    return "\n".join(lines)


def _load_template(lean_dir: Path, name: str) -> str:
    path = _template_path(lean_dir, name)
    return path.read_text(encoding="utf-8")


def _extract_int_tag(tags: list[str], prefix: str) -> int | None:
    for tag in tags:
        if not tag.startswith(prefix):
            continue
        raw = tag.split(":", 1)[1].strip()
        if raw.isdigit():
            return int(raw)
        return None
    return None


def _render_common(template: str, item: DatasetItem, candidate: str, heartbeats: int) -> str:
    context = item.context.strip()
    if not context:
        context = ""
    return (
        template.replace("{{IMPORTS}}", render_imports(item.imports))
        .replace("{{CONTEXT}}", context)
        .replace("{{CAND}}", candidate.strip())
        .replace("{{HEARTBEATS}}", str(heartbeats))
    )


def render_test1(lean_dir: Path, item: DatasetItem, candidate: str, heartbeats: int) -> str:
    template = _load_template(lean_dir, "Test1.lean.template")
    return _render_common(template, item, candidate, heartbeats)


def render_test2(
    lean_dir: Path,
    item: DatasetItem,
    candidate: str,
    heartbeats: int,
    prompt_version: str = BENCHMARK_PROMPT_VERSION,
) -> str:
    template = _load_template(lean_dir, "Test2.lean.template")
    rendered = _render_common(template, item, candidate, heartbeats)
    if item.family == "fin_truth_table":
        enum_cap = _extract_int_tag(item.tags, "enum_cap:")
        # Fail closed when tag metadata is missing or malformed.
        enum_cap = enum_cap if enum_cap is not None else 0
    elif item.family == "set_equality":
        set_enum_cap = _extract_int_tag(item.tags, "set_enum_cap:")
        enum_cap = set_enum_cap if set_enum_cap is not None else 0
    else:
        enum_cap = 0
    return (
        rendered.replace("{{EXPECTED}}", item.expected.strip())
        .replace("{{FAMILY}}", item.family)
        .replace("{{CHECK_KEY}}", item.semantic.check)
        .replace("{{FRAGMENT_KEY}}", fragment_for_item(item, prompt_version=prompt_version))
        .replace("{{ENUM_CAP}}", str(enum_cap))
    )

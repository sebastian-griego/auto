from __future__ import annotations

from pathlib import Path

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


def render_test2(lean_dir: Path, item: DatasetItem, candidate: str, heartbeats: int) -> str:
    template = _load_template(lean_dir, "Test2.lean.template")
    rendered = _render_common(template, item, candidate, heartbeats)
    return (
        rendered.replace("{{EXPECTED}}", item.expected.strip())
        .replace("{{FAMILY}}", item.family)
        .replace("{{CHECK_KEY}}", item.semantic.check)
    )

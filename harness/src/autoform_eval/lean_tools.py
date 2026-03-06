from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from .cache import JsonCache, stable_hash
from .lean_runner import classify_failure, run_lean_file
from .paths import default_cache_root, default_lean_dir


_JSON_PREFIX = "AUTOFORM_JSON:"


def _read_text_file(path: Path) -> str:
    if not path.exists():
        return ""
    return path.read_text(encoding="utf-8")


def _sources_root() -> Path:
    root = default_cache_root() / "lean_tools_sources"
    root.mkdir(parents=True, exist_ok=True)
    return root


def _results_cache() -> JsonCache:
    root = default_cache_root() / "lean_tools_results"
    root.mkdir(parents=True, exist_ok=True)
    return JsonCache(root)


def _tool_cache_key(
    *,
    tool_name: str,
    imports: list[str],
    payload: dict[str, Any],
) -> str:
    lean_dir = default_lean_dir()
    key_data = {
        "tool_name": tool_name,
        "imports": imports,
        "payload": payload,
        "lean_toolchain": _read_text_file(lean_dir / "lean-toolchain"),
        "lakefile_lean": _read_text_file(lean_dir / "lakefile.lean"),
    }
    return stable_hash(json.dumps(key_data, sort_keys=True))


def _write_tool_source(cache_key: str, source: str) -> Path:
    path = _sources_root() / f"{cache_key}.lean"
    if not path.exists() or _read_text_file(path) != source:
        path.write_text(source, encoding="utf-8")
    return path


def _dedupe_preserve_order(values: list[str] | None) -> list[str]:
    if not values:
        return []
    seen: set[str] = set()
    out: list[str] = []
    for value in values:
        token = value.strip()
        if not token or token in seen:
            continue
        seen.add(token)
        out.append(token)
    return out


def _render_module(imports: list[str], body: str) -> str:
    lines: list[str] = [f"import {module}" for module in imports]
    if lines:
        lines.append("")
    lines.append(body.rstrip())
    lines.append("")
    return "\n".join(lines)


def _run_plain_tool(
    *,
    tool_name: str,
    imports: list[str],
    payload: dict[str, Any],
    source: str,
    timeout_seconds: float,
) -> dict[str, Any]:
    cache = _results_cache()
    cache_key = _tool_cache_key(tool_name=tool_name, imports=imports, payload=payload)
    cached = cache.get(tool_name, cache_key)
    if cached is not None:
        return cached

    lean_file = _write_tool_source(cache_key, source)
    result = run_lean_file(default_lean_dir(), lean_file, timeout_seconds=timeout_seconds)
    out = {
        "okay": bool(result.ok),
        "bucket": "pass" if result.ok else classify_failure(result.stderr, result.timed_out, result.stdout),
        "stdout": result.stdout,
        "stderr": result.stderr,
        "elapsed_ms": result.elapsed_ms,
    }
    if not result.timed_out:
        cache.set(tool_name, cache_key, out)
    return out


def _run_json_tool(
    *,
    tool_name: str,
    imports: list[str],
    payload: dict[str, Any],
    source: str,
    timeout_seconds: float,
) -> dict[str, Any]:
    cache = _results_cache()
    cache_key = _tool_cache_key(tool_name=tool_name, imports=imports, payload=payload)
    cached = cache.get(tool_name, cache_key)
    if cached is not None:
        return cached

    lean_file = _write_tool_source(cache_key, source)
    result = run_lean_file(default_lean_dir(), lean_file, timeout_seconds=timeout_seconds)
    if not result.ok:
        out = {
            "okay": False,
            "bucket": classify_failure(result.stderr, result.timed_out, result.stdout),
            "stdout": result.stdout,
            "stderr": result.stderr,
            "elapsed_ms": result.elapsed_ms,
        }
        if not result.timed_out:
            cache.set(tool_name, cache_key, out)
        return out

    marker_payload: str | None = None
    for line in result.stdout.splitlines():
        if line.startswith(_JSON_PREFIX):
            marker_payload = line[len(_JSON_PREFIX) :]
            break

    if marker_payload is None:
        out = {
            "okay": False,
            "bucket": "tool_no_json",
            "stdout": result.stdout,
            "stderr": result.stderr,
            "elapsed_ms": result.elapsed_ms,
        }
        cache.set(tool_name, cache_key, out)
        return out

    try:
        parsed = json.loads(marker_payload)
        if not isinstance(parsed, dict):
            raise ValueError("tool JSON marker must encode an object")
    except Exception:  # noqa: BLE001
        out = {
            "okay": False,
            "bucket": "tool_json_parse_error",
            "stdout": result.stdout,
            "stderr": result.stderr,
            "elapsed_ms": result.elapsed_ms,
        }
        cache.set(tool_name, cache_key, out)
        return out

    out = dict(parsed)
    out["okay"] = bool(out.get("okay", False))
    out.setdefault("bucket", "pass" if out["okay"] else "semantic_fail")
    out["stdout"] = result.stdout
    out["stderr"] = result.stderr
    out["elapsed_ms"] = result.elapsed_ms
    cache.set(tool_name, cache_key, out)
    return out


def check_content(content: str, imports: list[str] | None = None, timeout_seconds: float = 30.0) -> dict[str, Any]:
    modules = _dedupe_preserve_order(imports)
    source = _render_module(modules, content)
    return _run_plain_tool(
        tool_name="check",
        imports=modules,
        payload={"content": content},
        source=source,
        timeout_seconds=timeout_seconds,
    )


def verify_proof(
    formal_statement: str,
    content: str,
    imports: list[str] | None = None,
    permitted_sorries: list[str] | None = None,
    timeout_seconds: float = 30.0,
) -> dict[str, Any]:
    modules = _dedupe_preserve_order(imports or ["Mathlib"])
    permitted = _dedupe_preserve_order(permitted_sorries)
    tool_import = "AutoformalizationEval.Tools.VerifyProof"
    all_imports = modules if tool_import in modules else [*modules, tool_import]
    if permitted:
        permitted_json = ", ".join(json.dumps(name) for name in permitted)
        verify_cmd = f"autoform_verify_proof [{permitted_json}]"
    else:
        verify_cmd = "autoform_verify_proof"
    source = _render_module(
        all_imports,
        "\n".join(
            [
                "set_option autoImplicit false",
                "",
                "namespace Spec",
                formal_statement.rstrip(),
                "end Spec",
                "",
                "namespace Cand",
                content.rstrip(),
                "end Cand",
                "",
                verify_cmd,
            ]
        ),
    )
    return _run_json_tool(
        tool_name="verify_proof",
        imports=all_imports,
        payload={
            "formal_statement": formal_statement,
            "content": content,
            "permitted_sorries": permitted,
        },
        source=source,
        timeout_seconds=timeout_seconds,
    )


def extract_theorems(content: str, imports: list[str] | None = None, timeout_seconds: float = 30.0) -> dict[str, Any]:
    modules = _dedupe_preserve_order(imports or ["Mathlib"])
    tool_import = "AutoformalizationEval.Tools.ExtractTheorems"
    all_imports = modules if tool_import in modules else [*modules, tool_import]
    source = _render_module(
        all_imports,
        "\n".join(
            [
                "set_option autoImplicit false",
                "",
                "namespace ExtractTmp",
                content.rstrip(),
                "end ExtractTmp",
                "",
                "autoform_extract_theorems",
            ]
        ),
    )
    return _run_json_tool(
        tool_name="extract_theorems",
        imports=all_imports,
        payload={"content": content},
        source=source,
        timeout_seconds=timeout_seconds,
    )

from __future__ import annotations

import subprocess
import time
from pathlib import Path

from .types import LeanRunResult


def _coerce_text(value: str | bytes | None) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value


def run_lean_file(lean_dir: Path, lean_file: Path, timeout_seconds: float) -> LeanRunResult:
    cmd = ["lake", "env", "lean", str(lean_file)]
    start = time.monotonic()
    try:
        completed = subprocess.run(
            cmd,
            cwd=str(lean_dir),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=timeout_seconds,
            check=False,
        )
        elapsed_ms = int((time.monotonic() - start) * 1000)
        return LeanRunResult(
            ok=completed.returncode == 0,
            timed_out=False,
            returncode=completed.returncode,
            elapsed_ms=elapsed_ms,
            stdout=completed.stdout,
            stderr=completed.stderr,
        )
    except subprocess.TimeoutExpired as exc:
        elapsed_ms = int((time.monotonic() - start) * 1000)
        return LeanRunResult(
            ok=False,
            timed_out=True,
            returncode=124,
            elapsed_ms=elapsed_ms,
            stdout=_coerce_text(exc.stdout),
            stderr=_coerce_text(exc.stderr),
        )


def classify_failure(stderr: str, timed_out: bool) -> str:
    if timed_out:
        return "timeout"
    if "[shape_fail]" in stderr:
        return "shape_fail"
    if "[semantic_fail]" in stderr:
        return "semantic_fail"
    if "expected" in stderr or "unexpected token" in stderr:
        return "lean_parse_fail"
    return "elab_fail"

from __future__ import annotations

import os
import signal
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


def _run_cmd(cmd: list[str], cwd: Path, timeout_seconds: float) -> LeanRunResult:
    start = time.monotonic()
    proc = subprocess.Popen(
        cmd,
        cwd=str(cwd),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    try:
        stdout, stderr = proc.communicate(timeout=timeout_seconds)
        elapsed_ms = int((time.monotonic() - start) * 1000)
        return LeanRunResult(
            ok=proc.returncode == 0,
            timed_out=False,
            returncode=proc.returncode,
            elapsed_ms=elapsed_ms,
            stdout=_coerce_text(stdout),
            stderr=_coerce_text(stderr),
        )
    except subprocess.TimeoutExpired as exc:
        # Kill the whole session so child Lean processes do not outlive the timeout.
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = proc.communicate()
        elapsed_ms = int((time.monotonic() - start) * 1000)
        return LeanRunResult(
            ok=False,
            timed_out=True,
            returncode=124,
            elapsed_ms=elapsed_ms,
            stdout=_coerce_text(stdout) or _coerce_text(exc.stdout),
            stderr=_coerce_text(stderr) or _coerce_text(exc.stderr),
        )


def run_lean_file(lean_dir: Path, lean_file: Path, timeout_seconds: float) -> LeanRunResult:
    cmd = ["lake", "env", "lean", str(lean_file)]
    return _run_cmd(cmd, lean_dir, timeout_seconds)


def classify_failure(stderr: str, timed_out: bool, stdout: str = "") -> str:
    text = f"{stderr}\n{stdout}"
    if timed_out:
        return "timeout"
    if "[shape_fail]" in text:
        return "shape_fail"
    if "[semantic_fail]" in text:
        return "semantic_fail"
    if "expected" in text or "unexpected token" in text:
        return "lean_parse_fail"
    return "elab_fail"

from __future__ import annotations

import sys
from pathlib import Path

from autoform_eval.lean_runner import _run_cmd


def test_run_cmd_timeout_returns_result(tmp_path: Path):
    result = _run_cmd(
        [sys.executable, "-c", "import time; time.sleep(5)"],
        tmp_path,
        timeout_seconds=0.1,
    )

    assert result.ok is False
    assert result.timed_out is True
    assert result.returncode == 124

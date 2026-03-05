from __future__ import annotations

import tempfile
from pathlib import Path

from .lean_runner import classify_failure, run_lean_file


def _find_repo_root() -> Path:
    cwd = Path.cwd().resolve()
    for candidate in (cwd, *cwd.parents):
        if (candidate / "lean" / "lean-toolchain").is_file() and (
            candidate / "harness" / "src" / "autoform_eval"
        ).is_dir():
            return candidate
    raise RuntimeError("could not locate repository root from current working directory")


def _render_case(
    *,
    cand: str,
    expected: str,
    family: str,
    check_key: str,
    fragment_key: str,
    enum_cap: int,
) -> str:
    return "\n".join(
        [
            "import AutoformalizationEval.Checks",
            "",
            "set_option autoImplicit false",
            "set_option maxHeartbeats 400000",
            "",
            "def cand : Prop :=",
            f"  {cand}",
            "",
            "def expected : Prop :=",
            f"  {expected}",
            "",
            f'autoform_check "{family}" "{check_key}" "{fragment_key}" {enum_cap}',
            "",
        ]
    )


def _assert_case(
    *,
    case_name: str,
    lean_dir: Path,
    work_dir: Path,
    content: str,
    expect_ok: bool,
    expect_stderr_contains: str | None = None,
) -> None:
    lean_path = work_dir / f"{case_name}.lean"
    lean_path.write_text(content, encoding="utf-8")

    result = run_lean_file(lean_dir, lean_path, timeout_seconds=30.0)
    if expect_ok:
        if not result.ok:
            bucket = classify_failure(result.stderr, result.timed_out, result.stdout)
            raise AssertionError(
                f"{case_name} expected success, got {bucket}\n"
                f"stderr:\n{result.stderr}\nstdout:\n{result.stdout}"
            )
        return

    if result.ok:
        raise AssertionError(f"{case_name} expected failure, but Lean succeeded")

    if expect_stderr_contains is not None and expect_stderr_contains not in result.stderr:
        if expect_stderr_contains in result.stdout:
            return
        bucket = classify_failure(result.stderr, result.timed_out, result.stdout)
        raise AssertionError(
            f"{case_name} missing failure marker {expect_stderr_contains!r} (bucket={bucket})\n"
            f"stderr:\n{result.stderr}\nstdout:\n{result.stdout}"
        )


def main() -> None:
    repo_root = _find_repo_root()
    lean_dir = repo_root / "lean"

    with tempfile.TemporaryDirectory(prefix="autoform_smoke_", dir="/tmp") as tmp:
        work_dir = Path(tmp)

        constant_ref = "∀ f : Fin 2 → Bool, f = f"
        _assert_case(
            case_name="fin_truth_table_fallback_constant_reference",
            lean_dir=lean_dir,
            work_dir=work_dir,
            content=_render_case(
                cand=constant_ref,
                expected=constant_ref,
                family="fin_truth_table",
                check_key="fin_truth_table",
                fragment_key="fin_truth_table_v1",
                enum_cap=16,
            ),
            expect_ok=False,
            expect_stderr_contains="[semantic_fail] truth_table_reference_constant",
        )

        non_constant_ref = "∀ f : Fin 2 → Bool, f 0 = true"
        _assert_case(
            case_name="fin_truth_table_fallback_nonconstant_reference",
            lean_dir=lean_dir,
            work_dir=work_dir,
            content=_render_case(
                cand=non_constant_ref,
                expected=non_constant_ref,
                family="fin_truth_table",
                check_key="fin_truth_table",
                fragment_key="fin_truth_table_v1",
                enum_cap=16,
            ),
            expect_ok=True,
        )

        set_eq = "((Set.univ : Set (Fin 3)) \\ Set.univ) = (∅ : Set (Fin 3))"
        _assert_case(
            case_name="set_equality_norm_v1_simple_pass",
            lean_dir=lean_dir,
            work_dir=work_dir,
            content=_render_case(
                cand=set_eq,
                expected=set_eq,
                family="set_equality",
                check_key="set_equality_norm",
                fragment_key="set_equality_norm_v1",
                enum_cap=64,
            ),
            expect_ok=True,
        )

    print("smoke tests passed")


if __name__ == "__main__":
    main()

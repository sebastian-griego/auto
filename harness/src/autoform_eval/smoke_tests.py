from __future__ import annotations

import tempfile
from pathlib import Path

from .lean_tools import check_content, extract_theorems, verify_proof
from .lean_runner import classify_failure, run_lean_file
from .paths import default_lean_dir


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


def _run_checker_smoke(lean_dir: Path) -> None:
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


def _run_tools_smoke() -> None:
    check_res = check_content(
        content="\n".join(
            [
                "set_option autoImplicit false",
                "",
                "theorem smoke_check : (1 + 1 : Nat) = 2 := by",
                "  decide",
            ]
        ),
        imports=["Init"],
        timeout_seconds=30.0,
    )
    if not bool(check_res.get("okay")):
        raise AssertionError(f"check_content expected success, got {check_res}")

    formal_add_comm = "\n".join(
        [
            "theorem add_comm (a b : Nat) : a + b = b + a := by",
            "  sorry",
        ]
    )
    cand_add_comm = "\n".join(
        [
            "theorem add_comm (a b : Nat) : a + b = b + a := by",
            "  exact Nat.add_comm a b",
        ]
    )
    verify_ok = verify_proof(
        formal_statement=formal_add_comm,
        content=cand_add_comm,
        imports=["Init"],
        timeout_seconds=30.0,
    )
    if not bool(verify_ok.get("okay")):
        raise AssertionError(f"verify_proof expected success, got {verify_ok}")

    cand_wrong = "\n".join(
        [
            "theorem add_comm (a b : Nat) : a + b = a + b := by",
            "  rfl",
        ]
    )
    verify_wrong = verify_proof(
        formal_statement=formal_add_comm,
        content=cand_wrong,
        imports=["Init"],
        timeout_seconds=30.0,
    )
    if bool(verify_wrong.get("okay")):
        raise AssertionError(f"verify_proof expected failure on wrong statement, got {verify_wrong}")
    failed_decls = verify_wrong.get("failed_declarations", [])
    if "add_comm" not in failed_decls:
        raise AssertionError(f"verify_proof wrong-statement case missing add_comm in failures: {verify_wrong}")

    cand_extra_sorry = "\n".join(
        [
            "theorem add_comm (a b : Nat) : a + b = b + a := by",
            "  exact Nat.add_comm a b",
            "",
            "theorem helper (n : Nat) : n = n := by",
            "  sorry",
        ]
    )
    verify_sorry = verify_proof(
        formal_statement=formal_add_comm,
        content=cand_extra_sorry,
        imports=["Init"],
        timeout_seconds=30.0,
    )
    if bool(verify_sorry.get("okay")):
        raise AssertionError(f"verify_proof expected failure on extra sorry helper, got {verify_sorry}")
    sorry_errors = verify_sorry.get("errors", [])
    if not any(str(err).startswith("candidate_sorry:") for err in sorry_errors):
        raise AssertionError(f"verify_proof extra-sorry case missing candidate_sorry error: {verify_sorry}")

    cand_extra_axiom = "\n".join(
        [
            "theorem add_comm (a b : Nat) : a + b = b + a := by",
            "  exact Nat.add_comm a b",
            "",
            "axiom extra_bad : True",
        ]
    )
    verify_axiom = verify_proof(
        formal_statement=formal_add_comm,
        content=cand_extra_axiom,
        imports=["Init"],
        timeout_seconds=30.0,
    )
    if bool(verify_axiom.get("okay")):
        raise AssertionError(f"verify_proof expected failure on extra candidate axiom, got {verify_axiom}")
    axiom_errors = verify_axiom.get("errors", [])
    if not any(str(err).startswith("extra_candidate_axiom:") for err in axiom_errors):
        raise AssertionError(f"verify_proof extra-axiom case missing extra_candidate_axiom error: {verify_axiom}")

    extract_content = "\n".join(
        [
            "def helper (n : Nat) : Nat := n + 1",
            "",
            "theorem t1 (n : Nat) : helper n = n + 1 := by",
            "  rfl",
            "",
            "theorem t2 (a b : Nat) : a + b = b + a := by",
            "  simpa using Nat.add_comm a b",
        ]
    )
    extract_res = extract_theorems(
        content=extract_content,
        imports=["Init"],
        timeout_seconds=30.0,
    )
    if not bool(extract_res.get("okay")):
        raise AssertionError(f"extract_theorems expected success, got {extract_res}")
    if int(extract_res.get("theorem_count", -1)) != 2:
        raise AssertionError(f"extract_theorems theorem_count mismatch: {extract_res}")
    theorem_rows = extract_res.get("theorems", [])
    theorem_names = {row.get("name") for row in theorem_rows if isinstance(row, dict)}
    if "t1" not in theorem_names or "t2" not in theorem_names:
        raise AssertionError(f"extract_theorems missing theorem names: {extract_res}")
    required_dep_fields = {
        "local_type_dependencies",
        "local_value_dependencies",
        "external_type_dependencies",
        "external_value_dependencies",
    }
    for row in theorem_rows:
        if not isinstance(row, dict):
            raise AssertionError(f"extract_theorems theorem row is not an object: {extract_res}")
        if not str(row.get("type", "")).strip():
            raise AssertionError(f"extract_theorems theorem type must be nonempty: {extract_res}")
        if not required_dep_fields.issubset(row.keys()):
            raise AssertionError(f"extract_theorems theorem row missing dependency fields: {extract_res}")


def main() -> None:
    lean_dir = default_lean_dir()
    _run_checker_smoke(lean_dir)
    _run_tools_smoke()
    print("smoke tests passed")


if __name__ == "__main__":
    main()

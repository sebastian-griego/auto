from __future__ import annotations

import tempfile
from pathlib import Path

from .lean_tools import check_content, extract_theorems, inspect_prop, verify_proof
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

    verify_no_cache = verify_proof(
        formal_statement=formal_add_comm,
        content=cand_add_comm,
        imports=["Init"],
        timeout_seconds=30.0,
        use_cache=False,
    )
    if "source_path" not in verify_no_cache or "cache_key" not in verify_no_cache:
        raise AssertionError(f"verify_proof no-cache result missing cache metadata: {verify_no_cache}")
    if verify_no_cache.get("cached") is not False:
        raise AssertionError(f"verify_proof no-cache result must report cached=False: {verify_no_cache}")

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

    preamble_twice = "def twice (n : Nat) : Nat := n + n"
    formal_twice = "\n".join(
        [
            "theorem twice_id (n : Nat) : twice n = n + n := by",
            "  sorry",
        ]
    )
    cand_twice = "\n".join(
        [
            "theorem twice_id (n : Nat) : twice n = n + n := by",
            "  rfl",
        ]
    )
    verify_with_preamble = verify_proof(
        formal_statement=formal_twice,
        content=cand_twice,
        imports=["Init"],
        preamble=preamble_twice,
        timeout_seconds=30.0,
        use_cache=False,
    )
    if not bool(verify_with_preamble.get("okay")):
        raise AssertionError(f"verify_proof preamble case expected success, got {verify_with_preamble}")

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

    preamble_extract = "def ext_helper (n : Nat) : Nat := n + 2"
    extract_with_preamble = extract_theorems(
        content="\n".join(
            [
                "theorem t3 (n : Nat) : ext_helper n = n + 2 := by",
                "  rfl",
            ]
        ),
        imports=["Init"],
        preamble=preamble_extract,
        timeout_seconds=30.0,
        use_cache=False,
    )
    if not bool(extract_with_preamble.get("okay")):
        raise AssertionError(f"extract_theorems preamble case expected success, got {extract_with_preamble}")
    preamble_rows = extract_with_preamble.get("theorems", [])
    if not preamble_rows or not isinstance(preamble_rows[0], dict):
        raise AssertionError(f"extract_theorems preamble case returned invalid theorem rows: {extract_with_preamble}")
    if not required_dep_fields.issubset(preamble_rows[0].keys()):
        raise AssertionError(f"extract_theorems preamble case missing dependency fields: {extract_with_preamble}")

    inspect_simple = inspect_prop(
        prop="∀ n : Nat, n = n",
        imports=["Init"],
        timeout_seconds=30.0,
        use_cache=False,
    )
    if not bool(inspect_simple.get("okay")):
        raise AssertionError(f"inspect_prop simple case expected success, got {inspect_simple}")
    if int(inspect_simple.get("leading_forall_count", -1)) != 1:
        raise AssertionError(f"inspect_prop simple case expected one leading forall, got {inspect_simple}")
    leading_foralls = inspect_simple.get("leading_foralls", [])
    if not isinstance(leading_foralls, list) or len(leading_foralls) != 1:
        raise AssertionError(f"inspect_prop simple case expected one leading forall entry, got {inspect_simple}")
    if not str(inspect_simple.get("type_pretty", "")).strip():
        raise AssertionError(f"inspect_prop simple case expected nonempty type_pretty, got {inspect_simple}")
    if "local_dependencies" not in inspect_simple or "external_dependencies" not in inspect_simple:
        raise AssertionError(f"inspect_prop simple case missing dependency fields: {inspect_simple}")

    inspect_with_preamble = inspect_prop(
        prop="∀ n : Nat, Good n",
        imports=["Init"],
        preamble="\n".join(
            [
                "namespace InspectTmp",
                "def Good (n : Nat) : Prop := n = n",
                "end InspectTmp",
            ]
        ),
        timeout_seconds=30.0,
        use_cache=False,
    )
    if not bool(inspect_with_preamble.get("okay")):
        raise AssertionError(f"inspect_prop preamble case expected success, got {inspect_with_preamble}")
    local_deps = inspect_with_preamble.get("local_dependencies", [])
    if "Good" not in local_deps:
        raise AssertionError(f"inspect_prop preamble case expected local dependency Good, got {inspect_with_preamble}")

    verify_internal_filter = verify_proof(
        formal_statement="\n".join(
            [
                "def pred0 (n : Nat) : Nat :=",
                "  match n with",
                "  | 0 => 0",
                "  | m + 1 => m",
            ]
        ),
        content="\n".join(
            [
                "def pred0 (n : Nat) : Nat :=",
                "  match n with",
                "  | 0 => 0",
                "  | m + 1 => m",
            ]
        ),
        imports=["Init"],
        timeout_seconds=30.0,
        use_cache=False,
    )
    if not bool(verify_internal_filter.get("okay")):
        raise AssertionError(f"verify_proof internal-filter case expected success, got {verify_internal_filter}")
    for field in ("spec_declarations", "candidate_declarations", "extra_candidate_declarations"):
        names = verify_internal_filter.get(field, [])
        if not isinstance(names, list):
            raise AssertionError(f"verify_proof internal-filter field {field} is not a list: {verify_internal_filter}")
        if any(("match_" in str(name) or "proof_" in str(name) or "_private" in str(name)) for name in names):
            raise AssertionError(f"verify_proof internal-filter case leaked internal names in {field}: {verify_internal_filter}")


def main() -> None:
    lean_dir = default_lean_dir()
    _run_checker_smoke(lean_dir)
    _run_tools_smoke()
    print("smoke tests passed")


if __name__ == "__main__":
    main()

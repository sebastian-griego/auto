# v1.1 Family Expansion Plan

Date: 2026-02-25

## Scope Goal

Add one meaningful deterministic family without changing frozen v1 results.

Chosen family for v1.1: **`set_equality` upgrade** (replace placeholder `set_equality_norm_v0` with a real deterministic checker).

## Why This Family

- `set_equality` is already wired but currently Tier B placeholder (`isDefEq` only).
- Upgrading it makes the benchmark more convincing without adding theorem-search nondeterminism.
- It addresses the explicit v1 concern that defeq-only `set_equality` should not be a headline family.

## v1.1 Fragment Contract

- Family: `set_equality`
- Check key: `set_equality_norm`
- New fragment key: `set_equality_norm_v1`
- Accepted semantic form (deterministic subset):
  - Outer binders may include finite domains already supported by `fin_truth_table` (`Bool`, `Fin n`, small nullary enums, small `Fintype` fallback with cap).
  - Set target type must be finite and decidable.
  - Body shape must be direct set equality over that target type (`A = B`).
  - Extensional rewrites like `∀ x, x ∈ A ↔ x ∈ B` are out-of-fragment for v1.1 and should be rejected by shape checks.

## Checker Design (Deterministic)

Implement `Families.checkSetEquality` as finite extensional evaluation:

1. Parse/validate binder domains and enforce an enum cap.
2. Enumerate finite assignments for leading finite binders.
3. For each assignment, evaluate both candidate and expected set expressions extensionally over every element of the finite set domain.
4. Fail fast on first witness mismatch with `[semantic_fail]` tag and witness payload.
5. Reject constant/trivial references if needed (analogous to truth-table strength checks).

Determinism controls:

- No proof search tactics.
- `decide`/`whnf`/`reduce` only.
- Per-item cap tag (proposed: `set_enum_cap:<N>`) enforced in validator and Lean checker.

## Required Harness/Validator Updates

- Add fragment mapping for `set_equality_norm_v1`.
- Extend validator static checks:
  - enforce `set_enum_cap` tag on `set_equality` rows,
  - enforce finite-domain eligibility for evaluated set type,
  - mutation checks must produce at least one elaborating mutant rejected by shape/semantic checks.
- Keep v1 files untouched (`dataset/test.jsonl`, prompt `v1.0.0`, existing v1 baselines).

## Dataset Plan (v1.1)

- Add **50 to 200** new `dev` items for `set_equality`.
- Suggested target: **80** rows (balanced operator patterns).
- Patterns to cover:
  - union/intersection identities
  - distributivity forms
  - difference/complement rewrites
  - idempotence/absorption forms
- Keep `test` unchanged for v1; define new v1.1 holdout additions separately.

## Acceptance Criteria

- New checker passes deterministic reruns.
- Validator catches malformed/weak set-equality rows.
- `dev` validates end-to-end with new rows.
- New v1.1 baseline run is generated and promoted without rewriting v1 artifacts.

## Explicit v1 Compatibility

- No edits to frozen v1 prompt, checker behavior used by v1 runs, or `dataset/test.jsonl`.
- All v1 headline numbers remain reproducible from tag `v1-freeze-20260225`.

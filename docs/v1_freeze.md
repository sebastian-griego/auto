# v1 Freeze Note

Date: 2026-02-25

This note freezes the v1 benchmark surface area for headline results.

## Frozen Surfaces

- Prompt version: `v1.0.0` (`harness/src/autoform_eval/prompt.py`).
- Holdout test split contents: `dataset/test.jsonl`.
  - `sha256`: `bc3e954f113729043c0f29f53d6862700ab16ba339f443cde6a7ee124f0228cc`
- Split definitions and counts:
  - `pilot`: 15 rows (`sha256`: `57683c39ba08c89088a7cec5f7fd8921dcc175fed47c9f1da1afd8b82f126909`)
  - `dev`: 100 rows (`sha256`: `77044f1078df92e36d2180a02a3e035f13c5adf67b9ce78efb78df025da12b49`)
  - `test`: 200 rows (`sha256`: `bc3e954f113729043c0f29f53d6862700ab16ba339f443cde6a7ee124f0228cc`)
- Checker/toolchain versions:
  - Lean toolchain: `leanprover/lean4:v4.12.0` (`lean/lean-toolchain`)
  - Mathlib revision: `v4.12.0` (`lean/lakefile.lean`)
  - Dataset item `checker_version`: `1.0`
- Family semantic keys currently used for v1:
  - `ring_identity_norm_v1`
  - `fin_truth_table_v1`

## Change Policy

- Any change to prompt text/version, checker semantics, split definitions, or `dataset/test.jsonl` requires a benchmark version bump and a new baseline set.
- `test` split edits remain critical-fix-only and must refresh this freeze note with new hashes.

# Families

## Tier A (priority)
- `ring_identity` -> `ring_identity_norm`
- `fin_truth_table` -> `fin_truth_table`

## Tier B (after stabilization)
- `set_equality` -> `set_equality_norm`
- linear inequality fragment (TBD)

## Notes
- `ring_identity_norm` currently supports a deterministic restricted grammar:
  binders, natural literals, `+`, `*`, and equation-side symmetry.
- `fin_truth_table` currently enumerates leading finite binders in a deterministic fragment:
  `Bool`, concrete `Fin n`, and small nullary enum inductives.
- Fragment keys are enforced in Test2:
  - `ring_identity_norm_v1`
  - `fin_truth_table_v1`
  - `set_equality_norm_v0` (Tier B placeholder)
- `fin_truth_table` uses a per-item enum cap (from `enum_cap:<N>` tag) rendered into Test2 and checked in Lean.

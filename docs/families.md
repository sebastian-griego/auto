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
- `fin_truth_table` currently enumerates leading `Bool` quantifiers with a fixed cap.
- Extend finite-domain support to small `Fin n` and enums in the next slice.

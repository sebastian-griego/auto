# Families

## Supported Families
- `ring_identity` -> `ring_identity_norm`
- `fin_truth_table` -> `fin_truth_table`
- `set_equality` -> `set_equality_norm`
- `linear_inequality` -> `linear_inequality_norm`

## Notes
- `ring_identity_norm` currently supports a deterministic restricted grammar:
  binders, natural literals, `+`, `*`, and equation-side symmetry.
  v1 (`ring_identity_norm_v1`) uses strict binder-position matching.
  v2 (`ring_identity_norm_v2`) is invariant to leading binder permutations.
- `fin_truth_table` currently enumerates leading finite binders in a deterministic fragment:
  `Bool`, concrete `Fin n`, small nullary enum inductives, and finite binders with
  `Fintype.card` reducible to a numeral.
  Canonical check key is `fin_truth_table`; `fin_truth_table_norm` is accepted as an alias.
  Parenthesize Bool connectives inside equality, e.g. `(a && b) = false` (not `a && b = false`).
  The semantic non-constant reference guard (`truth_table_reference_constant`) is enforced in both
  explicit enumeration and `Fintype` fallback paths.
- Allowed provenance source kinds: `mathlib_decl`, `textbook`, `competition`,
  `assistant_generated`, `other`.
- `context` may include local `def` declarations when needed (for helper functions/constants).
- Fragment keys are enforced in Test2:
  - `ring_identity_norm_v1`
  - `ring_identity_norm_v2`
  - `fin_truth_table_v1`
  - `linear_inequality_norm_v1`
  - `set_equality_norm_v0` (compatibility path)
  - `set_equality_norm_v1` (deterministic finite assignment + extensional side comparison)
- `fin_truth_table` uses a per-item enum cap (from `enum_cap:<N>` tag) rendered into Test2 and checked in Lean.
- `set_equality_norm_v1` uses per-item `set_enum_cap:<N>` metadata.
- `set_equality` rows should keep expected terms in direct equality form (`A = B`) with set-typed sides.
  Extensional membership forms (`∀ x, x ∈ A ↔ x ∈ B`) are intentionally out of fragment.
- `linear_inequality_norm_v1` is a strict, conservative affine fragment:
  leading binders must be `Nat` or `Int`, and the body must be `lhs < rhs` or `lhs <= rhs`.
  Allowed expression syntax is bound variables, nonnegative numerals, `+`, parentheses, and numeral scalar multiplication.
  The deterministic checker normalizes both sides to a canonical affine constraint
  `a1*x1 + ... + an*xn + c < 0` or `a1*x1 + ... + an*xn + c <= 0` in quantified-binder order,
  then compares the exact normalized relation kind, coefficients, and constant.
  Intentionally unsupported: nonlinear multiplication, division, subtraction surface syntax, negative literals,
  `abs`, `max`, `min`, `let`, lambdas, `if`, theorem declarations, `by`, and `sorry`.
  Intentionally unsupported equivalences include inequality reversal, `<` vs `<=`, factor cancellation,
  and solving-style rewrites beyond direct affine normalization.

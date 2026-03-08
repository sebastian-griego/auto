# Add Dataset Item

## Template
```json
{
  "schema_version": "1.0",
  "checker_version": "1.0",
  "id": "unique_id",
  "nl": "Natural language statement",
  "imports": ["Mathlib"],
  "context": "variable (R : Type) [Semiring R]",
  "expected": "∀ x y : R, x + y = y + x",
  "family": "ring_identity",
  "tier": "A",
  "split": "pilot",
  "tags": ["tier_a"],
  "semantic": {
    "kind": "normalized_ref",
    "check": "ring_identity_norm"
  },
  "provenance": {
    "source_kind": "other",
    "source_ref": "source-or-module",
    "license": "CC-BY-4.0"
  }
}
```

## Rules
- Keep `context` minimal.
- `context` may include local `def` declarations when helper definitions are needed.
- `expected` must be a Lean `Prop` term.
- Choose `semantic.kind` and `semantic.check` consistent with the family.
- Fill provenance fields for every row.
- Allowed `provenance.source_kind`: `mathlib_decl`, `textbook`, `competition`, `assistant_generated`, `other`.
- For `fin_truth_table`, include an `enum_cap:<N>` tag and keep `N <= 256`.
- For `fin_truth_table`, use canonical `semantic.check = fin_truth_table` (`fin_truth_table_norm` is accepted as an alias).
- For `set_equality`, include a `set_enum_cap:<N>` tag and keep `N <= 4096`.
- For `set_equality`, expected terms should be direct equality (`A = B`) with set-typed sides, not extensional rewrites like `∀ x, x ∈ A ↔ x ∈ B`.
- For `linear_inequality`, use `semantic.kind = normalized_ref` and `semantic.check = linear_inequality_norm`.
- For `linear_inequality`, expected terms must stay inside fragment `linear_inequality_norm_v1`:
  leading binders only over `Nat`/`Int`, body only `lhs < rhs` or `lhs <= rhs`,
  and affine syntax restricted to bound variables, nonnegative numerals, `+`, parentheses, and numeral scalar multiplication.
- For `linear_inequality`, do not use subtraction surface syntax, negative literals, nonlinear multiplication, division,
  `abs`, `max`, `min`, `let`, lambdas, or `if`.
- Optional: set `fragment:<key>` in tags to override the default fragment key derived from `semantic.check`.
- For `fin_truth_table`, the deterministic checker supports leading binders over `Bool`, concrete `Fin n`, small nullary enum inductives declared in `context`, and any type with a `Fintype` instance whose `Fintype.card` reduces to a numeral in Lean.
- For `fin_truth_table`, set `enum_cap` to the assignment product of leading finite binders. Validator recomputes this and enforces consistency.
- For `fin_truth_table`, semantic non-constant reference guarding (`truth_table_reference_constant`) is enforced in both explicit assignment enumeration and the `Fintype` fallback path.
- For enum binders, keep constructors nullary and small enough that full assignment product remains under the cap.
- For `set_equality`, choose `set_enum_cap` so it is at least `max(outer_assignment_count, carrier_size)`.

## Common mistakes
- Missing nested `semantic` or `provenance` fields.
- Forbidden command tokens inside `context`/`expected` snippets.
- For `linear_inequality`, using subtraction or negative literals instead of moving terms across the relation.
- For `linear_inequality`, using `x * y`, division, or helper syntax (`let`, `if`, lambdas) that leaves the strict affine fragment.
- Mutation tests all passing due to weak checker.

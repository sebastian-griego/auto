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
- `expected` must be a Lean `Prop` term.
- Choose `semantic.kind` and `semantic.check` consistent with the family.
- Fill provenance fields for every row.
- For `fin_truth_table`, include an `enum_cap:<N>` tag and keep `N <= 256`.
- Optional: set `fragment:<key>` in tags to override the default fragment key derived from `semantic.check`.
- For `fin_truth_table`, the deterministic checker supports leading binders over `Bool`, concrete `Fin n`, and small nullary enum inductives declared in `context`.
- For `fin_truth_table`, set `enum_cap` to the assignment product of leading finite binders. Validator recomputes this and enforces consistency.
- For enum binders, keep constructors nullary and small enough that full assignment product remains under the cap.

## Common mistakes
- Missing nested `semantic` or `provenance` fields.
- Forbidden command tokens inside `context`/`expected` snippets.
- Mutation tests all passing due to weak checker.

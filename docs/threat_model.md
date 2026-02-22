# Threat Model (v1 bootstrap)

## Potential gaming behaviors
- Returning top-level Lean commands instead of a proposition term.
- Returning vacuous propositions.
- Exploiting theoremhood checks with semantically unrelated but provable statements.
- Prompt injection in context text.

## Defenses in v1
- Lexical hard rejections (`theorem`, `lemma`, `def`, `example`, `namespace`, `section`, `by`, `sorry`).
- Test1 elaboration contract (`cand : Prop`).
- Shape guard before family semantics.
- Family checker dispatch with deterministic checks.
- Family fragment keys are passed into Test2 and enforced by checker dispatch.
- `fin_truth_table` enum caps are passed per item into Test2 and enforced in Lean.
- Mutation tests in validator.
- Provider/API failures are bucketed as `provider_error` and kept separate from Lean failure buckets.

## Remaining limitations
- Tier B families are placeholders.
- Tier A checkers still operate on deliberately restricted fragments; equivalent out-of-fragment terms fail by design.

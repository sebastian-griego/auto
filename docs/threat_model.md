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
- Mutation tests in validator.

## Remaining limitations
- Bootstrap family checkers still use strict expression comparison and must be upgraded.
- Tier B families are placeholders.

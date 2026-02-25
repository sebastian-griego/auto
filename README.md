# Autoformalization Eval Suite (v1 bootstrap)

This repository evaluates NL -> Lean 4 `Prop` autoformalization quality with a two-stage check:

1. **Test 1**: candidate elaborates as `Prop`
2. **Test 2**: deterministic semantic check (shape guard + family checker)

## What v1 measures
- Model ability to output well-formed Lean `Prop` terms from natural language.
- Model ability to preserve semantics under deterministic family-specific checks.

## What v1 does not measure
- Proof generation quality.
- Broad theorem-proving search success.

## Why trivial outputs should fail
- Output contract rejects command-like outputs and `by`/`sorry`.
- Shape guard enforces structural compatibility with reference propositions.
- Family checks compare meaning in deterministic, restricted fragments.
- Validator runs mutation checks to ensure non-triviality.

## Run accounting
- Provider/API failures are bucketed as `provider_error` (separate from Lean failure buckets).
- Transient provider failures are retried and not cached as sticky provider errors.
- Summary semantic rates exclude `provider_error` attempts from denominators.
- Prompt construction is versioned (`--prompt-version`, default `v1.0.0`) and recorded in run artifacts.

## Quickstart
```bash
./scripts/setup.sh
```

`setup.sh` also enables the repository hook path (`core.hooksPath=.githooks`) so the local pre-commit secrets guard runs before each commit.

Then:
```bash
cd harness
python -m autoform_eval.cli validate --split pilot
```

Run a tiny mock eval:
```bash
cd harness
python -m autoform_eval.cli run --split pilot --models openai:mock --mock --k 1
```

## Pinned environment
- Lean toolchain: see `lean/lean-toolchain`
- mathlib revision: see `lean/lakefile.lean`

## Split policy
- `pilot`: small, stable sanity/baseline split.
- `dev`: active iteration split for checker and dataset refinement.
- `test`: holdout split. Do not edit except critical correctness fixes.
- Any `test` change should be treated as a benchmark version bump.

## Project docs
- Full plan: `docs/plan_v1.md`
- Protocol: `docs/protocol.md`
- Threat model: `docs/threat_model.md`
- Add item guide: `docs/add_item.md`
- Families overview: `docs/families.md`

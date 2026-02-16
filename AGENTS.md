# Autoformalization Eval Suite: Agent Operating Guide

## Purpose
This repository implements the NL -> Lean 4 `Prop` autoformalization evaluation suite described in `docs/plan_v1.md`.
Future Codex sessions must treat `docs/plan_v1.md` as the source-of-truth specification for v1 scope and constraints.

## Execution Rules
- Keep changes aligned with Milestone 1 first.
- Prefer deterministic checks over broad theorem proving.
- Preserve the two-stage pipeline:
  - Test 1: `cand : Prop` elaboration.
  - Test 2: shape + family semantic check.
- Any new checker failure intended for bucketing must include tags:
  - `[shape_fail]`
  - `[semantic_fail]`
- Do not add non-deterministic tactics to semantic checks.
- Keep Lean and mathlib pinned.
- Never add API keys or secrets to repository files.

## Current Project Phase
The repository is in bootstrap status for Milestone 1.

Primary next tasks:
1. Implement Lean checker core and Tier A families.
2. Implement harness parsing, rendering, Lean runner, caching, and CLI.
3. Build dataset validator with mutation tests.
4. Add pilot dataset items and provenance.
5. Complete CI workflows.

## Milestone 1 Definition of Done
- Pilot dataset validates in CI.
- Harness writes `results.jsonl`, `summary.json`, `report.md`.
- Buckets are stable and informative.
- Reproducible setup works from clean machine using README steps.

## Working Agreements for Future Sessions
- Read `docs/plan_v1.md` and `docs/status.md` before coding.
- Update `docs/status.md` whenever milestone progress changes.
- Prefer small, verifiable increments and run local checks after edits.
- Keep file layout consistent with section 4 of `docs/plan_v1.md`.

## Key Paths
- Plan: `docs/plan_v1.md`
- Progress tracker: `docs/status.md`
- Dataset: `dataset/`
- Lean checker: `lean/AutoformalizationEval/`
- Harness: `harness/src/autoform_eval/`
- CI: `.github/workflows/`

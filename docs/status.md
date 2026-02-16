# Status Tracker

## Snapshot
- Date: 2026-02-16
- Phase: Milestone 1 bootstrap
- Status: In progress

## Completed
- [x] Repository skeleton aligned with v1 plan
- [x] Source-of-truth plan committed at `docs/plan_v1.md`
- [x] Agent guide committed at `AGENTS.md`
- [x] Lean project builds with checker dispatch and tagged failures
- [x] Harness CLI supports `validate`, `run`, and `report`
- [x] Dataset validator runs schema/static/self-check/mutation flow
- [x] CI workflow scaffolds added for build, validation, tiny eval, and secrets scan
- [x] Tier A ring checker upgraded from defeq to deterministic polynomial-style normalization
- [x] Tier A finite truth-table checker upgraded to explicit Bool assignment enumeration
- [x] Pilot split expanded to 8 Tier A rows (4 ring + 4 finite truth-table)
- [x] Expanded pilot split validates locally with mutation checks
- [x] Shape guard binder-type checks restored with context-safe fvar remapping
- [x] Validator mutation operators strengthened and deduplicated
- [x] Validator now enforces per-test elapsed-time budgets (`budget1_ms` / `budget2_ms`)
- [x] Validator enforces `enum_cap` tags for `fin_truth_table` rows
- [x] Mutation gate now requires at least one shape/semantic rejection from an elaborating mutant
- [x] Lean failure bucketing now scans both stdout and stderr (Lean may emit errors on stdout)
- [x] `fin_truth_table` extended beyond Bool to deterministic `Fin n` enumeration
- [x] Pilot split expanded to 10 Tier A rows (including mixed Bool/Fin cases)

## In Progress
- [ ] Expand `pilot.jsonl` from 8 bootstrap rows to ~30 curated rows with stronger provenance
- [ ] Extend finite-domain checker from `Bool`/`Fin n` to small enum fragments
- [ ] Add determinism checks across repeated validator runs (beyond timeout/budget limits)

## Next Concrete Slice
1. Add small enum support to finite truth-table enumeration and tag-based cap checks.
2. Add rerun-based determinism assertions in validator outputs.
3. Grow pilot set toward 30 rows with curated provenance (not synthetic placeholders).

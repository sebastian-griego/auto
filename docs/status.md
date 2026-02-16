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
- [x] Pilot split expanded to 30 Tier A rows (ring + Bool/Fin finite-domain cases)
- [x] Validator supports determinism rerun assertions (`--determinism-repeats`, jitter checks)
- [x] Validator enforces unique item IDs and split consistency per row
- [x] `fin_truth_table` supports small enum inductives with nullary constructors
- [x] Pilot split includes Bool, `Fin n`, and enum finite-domain truth-table rows
- [x] Reporting upgraded with per-model slices and deterministic Pass@k aggregation
- [x] Run artifacts now include rendered/log file paths and optional prompt text

## In Progress
- [ ] Replace synthetic pilot rows with curated provenance-complete rows from public sources
- [ ] Run determinism reruns in broader CI coverage while keeping job time bounded

## Next Concrete Slice
1. Curate and replace synthetic pilot rows with provenance-complete sourced rows.
2. Add a larger determinism rerun CI gate (beyond current mixed smoke subset).
3. Add leakage/dedup checks across future dev/test splits.

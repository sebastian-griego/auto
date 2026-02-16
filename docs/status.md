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

## In Progress
- [ ] Expand `pilot.jsonl` from 8 bootstrap rows to ~30 curated rows with stronger provenance
- [ ] Tighten shape guard to robust binder-type and outer-form checks
- [ ] Add stronger mutation operators and determinism budget enforcement

## Next Concrete Slice
1. Extend finite-domain checker beyond Bool to small `Fin n`/enum fragments with deterministic caps.
2. Restore binder-type shape checks in a context-safe way and keep stable bucketing.
3. Grow pilot set toward 30 rows with curated provenance (not synthetic placeholders).

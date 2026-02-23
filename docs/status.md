# Status Tracker

## Snapshot
- Date: 2026-02-23
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
- [x] Pilot split includes Bool and `Fin n` finite-domain truth-table rows
- [x] Reporting upgraded with per-model slices and deterministic Pass@k aggregation
- [x] Run artifacts now include rendered/log file paths and optional prompt text
- [x] Lean runner timeout handling now terminates process groups to avoid orphan Lean processes
- [x] Validator adds one-time Lean warmup to stabilize cold-start timing budgets
- [x] Pilot split rows replaced with curated public-source provenance (Lean core + mathlib, Apache-2.0)
- [x] Curated pilot passes local `make validate` and determinism reruns (`--determinism-repeats 3 --determinism-jitter-ms 5000`)
- [x] End-to-end mock baseline run produced artifacts at `results/runs/20260217_213234`
- [x] `fin_truth_table` semantic checker rejects constant reference truth tables
- [x] Pilot `fin_truth_table` references rewritten to non-constant assignments; local validate passes
- [x] Dataset JSONL formatter script added at `scripts/format_jsonl.py`
- [x] Baseline artifact promotion/repro steps documented at `results/baselines/README.md`
- [x] End-to-end mock baseline run produced artifacts at `results/runs/20260218_031159`
- [x] Local pre-commit secrets guard added at `.githooks/pre-commit` and wired via `scripts/setup.sh`
- [x] Provider adapter compatibility fixes landed for OpenAI Responses API fallback and Gemini thinking-budget handling
- [x] Real provider baseline artifacts promoted at `results/baselines/pilot/20260218_185307` (`k=1`) and `results/baselines/pilot/20260218_185732` (`k=3`)
- [x] Candidate parsing now unwraps single- and double-backtick whole-term inline code wrappers before Lean checks
- [x] Harness run metadata now auto-detects pinned `mathlib` revision from `lean/lakefile.lean` when `--mathlib-rev` is unset
- [x] Gemini-only pilot baseline refreshed after parser/metadata fixes at `results/baselines/pilot/20260220_032149` (`k=1`)
- [x] CI `validate_dataset` now asserts pilot split stability (`total == 30`, `invalid == 0`)
- [x] CI determinism smoke subset expanded from 8 to 13 mixed-family pilot rows
- [x] Validator now enforces NL/expected duplicate checks within split and cross-split leakage checks
- [x] CI now validates `dev` split with schema/leakage checks (`--skip-lean`)
- [x] Report sample failures now include stderr/stdout excerpts so Lean stdout-only errors are visible
- [x] `validate_dataset` CI now mirrors Lean cache/build setup (`~/.elan`, `lean/.lake`, `lake build`)
- [x] `dev` split initialized with 20 Tier A rows (`ring_identity` + `fin_truth_table`)
- [x] Local `dev` validation passes with and without Lean checks (`--timeout1 12 --timeout2 25`)
- [x] Baseline report regenerated post-report-fix at `results/baselines/pilot/20260220_032149/report.md`
- [x] Runner now buckets provider/API generation failures as `provider_error` (separate from Lean failures)
- [x] Summary/report denominators now exclude `provider_error` attempts while still reporting provider error counts/rates
- [x] Benchmark prompt is now versioned (`v1.0.0`) and recorded per attempt (`prompt_version`)
- [x] Test2 now consumes explicit fragment keys and enforces checker/key compatibility in Lean
- [x] `fin_truth_table` Test2 now consumes per-item `enum_cap` values rendered from tags
- [x] Validator now recomputes finite assignment caps from item binders and enforces `enum_cap` tag consistency
- [x] Runner now retries transient provider errors and avoids caching them as sticky `provider_error` failures
- [x] CI now validates `test` split schema/leakage checks (`--skip-lean`)

## In Progress
- [ ] Add refreshed Gemini pilot baseline at `k=3` for post-parser-fix comparison
- [ ] Keep `dev` Lean smoke coverage bounded in CI as item count grows

## Next Concrete Slice
1. Refresh Gemini pilot baseline at `k=3` and promote artifacts.
2. Expand `dev` with another curated Tier A batch while preserving cross-split leakage constraints.
3. Populate and freeze holdout `test` split once dev loop stabilizes.

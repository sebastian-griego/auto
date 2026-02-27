# Status Tracker

## Snapshot
- Date: 2026-02-27
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
- [x] CI `validate_dataset` now asserts pilot split stability (`total == 15`, `invalid == 0`)
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
- [x] CI smoke subsets now pick deterministic per-family rows by sorted IDs (ID-agnostic) and emit proper JSONL newlines
- [x] CI smoke validations now write reports under `/tmp` instead of overwriting `dataset/validation_report.json`
- [x] CI adds a tiny Lean smoke subset for `test` split
- [x] Split policy now marks `test` as holdout (critical-fix-only; version bump on edits)
- [x] Enum-context rows fixed to use valid Lean deriving syntax (`deriving DecidableEq` / `deriving Fintype`) in `dev` and `test`
- [x] Targeted full Lean checks for affected enum-context subsets pass (`dev`: 6/6, `test`: 6/6)
- [x] Gemini-only pilot baselines refreshed and promoted at `results/baselines/pilot/20260224_233417` (`k=1`) and `results/baselines/pilot/20260224_233637` (`k=3`)
- [x] Full Lean-backed validation reruns pass locally on `dev` (`total=100`, `invalid=0`) and `test` (`total=200`, `invalid=0`) after fixing `ftt_dev_0011` shape compatibility
- [x] Gemini dev baseline promoted at `results/baselines/dev/20260225_051505_dev_gemini_k1_v1` (`k=1`, `prompt=v1.0.0`, combined rate `0.830`)
- [x] v1 freeze policy and hashes documented at `docs/v1_freeze.md`
- [x] Freeze tag created: `v1-freeze-20260225`
- [x] Frozen Gemini test baseline promoted at `results/baselines/test/20260225_053241_test_gemini_k1_v1` (`k=1`, `prompt=v1.0.0`, combined rate `0.899`, provider errors `1`)
- [x] v1 baseline analysis report added at `docs/v1_results.md` and linked from README
- [x] v1.1 deterministic family expansion plan added at `docs/v1_1_plan.md`
- [x] Added `ring_identity_norm_v2` checker variant (binder-permutation invariant) while preserving strict `ring_identity_norm_v1`
- [x] Lean checker dispatch now accepts both ring fragment keys: `ring_identity_norm_v1` and `ring_identity_norm_v2`
- [x] Prompt versioning now supports `v1.0.0` and `v1.1.0` (default `v1.1.0`), with ring fragment mapping switched to `ring_identity_norm_v2` in `v1.1.0`
- [x] `fin_truth_table` prompt rules now explicitly require parentheses for `&&`/`||` inside equality
- [x] Validator now lints `fin_truth_table` expected terms for unparenthesized top-level Bool connective equality sides
- [x] Added ring regression harness (`scripts/run_ring_identity_regression.sh`) with Lean fixtures for v1/v2 binder reorder and real mismatch checks
- [x] Targeted replay of frozen test ring semantic failures under `v1.1.0` flipped 16/17 to pass; `ring_test_0016` remained the only semantic failure
- [x] Lean-backed pilot validation passes with prompt version `v1.1.0` (`total=15`, `invalid=0`)
- [x] Offline replay of frozen dev candidates under `v1.1.0` yields combined `0.950` and `ring_identity` combined `1.000` (previous frozen dev combined `0.830`)
- [x] Ring prompt rules now explicitly warn about noncommutative multiplication order (`do not reorder factors`)
- [x] Protocol docs now distinguish current default prompt (`v1.1.0`) from frozen-v1 reproduction (`v1.0.0`)
- [x] Added `set_equality_norm_v1` deterministic checker path (finite assignment enumeration with enum cap + extensional side comparison, with equation-side swap)
- [x] Preserved compatibility path `set_equality_norm_v0` and versioned dispatch now accepts both `_v0` and `_v1`
- [x] Prompt mapping for `set_equality_norm` now targets `set_equality_norm_v1` under `v1.1.0`
- [x] Validator/render now support `set_enum_cap:<N>` tags for `set_equality` items
- [x] Added set-equality regression harness (`scripts/run_set_equality_regression.sh`) with pass/fail Lean fixtures
- [x] Lean-backed pilot validation still passes with prompt version `v1.1.0` (`total=15`, `invalid=0`) after set-equality checker upgrade

## In Progress
- [ ] Verify CI is green on latest commits after pushing freeze/baseline artifacts

## Next Concrete Slice
1. If desired, add a `k=3` dev baseline companion run for calibration.
2. Open v1.1 implementation branch for `set_equality_norm_v1` checker and validator/tag support.
3. Prepare release notes that reference freeze tag + baseline artifact directories.

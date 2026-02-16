# Publishable autoformalization eval suite v1 plan

## 1) Outcome and non-goals

### 1.1 Outcome

A public repository that anyone can run to evaluate frontier models on NL → Lean 4 `Prop` autoformalization with:

- A validated dataset of natural-language statements, each paired with:
  - Lean imports
  - Lean context
  - A reference proposition `expected : Prop`
  - A semantic checking strategy that is deterministic and fast
- A two-stage checker per item:
  - Test 1: candidate elaborates as `Prop`
  - Test 2: meaning check using shape checks plus deterministic family checks
- A harness that:
  - runs OpenAI and Gemini adapters
  - caches model responses and Lean outcomes
  - writes `results.jsonl`, `summary.json`, and `report.md`
  - produces baseline tables and failure analysis
- CI that:
  - builds the pinned Lean project
  - validates dataset determinism and strength
  - prevents drift and dataset rot
  - blocks accidental secret commits

### 1.2 Non-goals for v1

- Do not measure proof generation.
- Do not include semantics that depend on unbounded proof search.
- Do not aim for maximal coverage of all mathlib domains in v1.
- Do not optimize for throughput until correctness and determinism are stable.

---

## 2) Core design principles

1. **Lean is the arbiter**
   String rules are only for early hard rejections and safety. Parsing and elaboration decide Test 1.

2. **Semantic checks must not pass due to theoremhood**
   Avoid “prove `cand ↔ expected`” as the primary mechanism. Prefer canonicalization, reification, evaluation, or decision procedures that compare candidate and reference meaning.

3. **Determinism first**
   Use strict timeouts plus Lean heartbeats. Minimize tactics with unpredictable search behavior.

4. **Validator is a first-class deliverable**
   CI must prevent silent degradation. Every item must remain checkable within the budget.

5. **Reproducibility is a feature**
   Pin Lean and mathlib. Record toolchain identifiers. Cache by content hashes.

---

## 3) Evaluation contract

### 3.1 Model output contract v1

The model must output a single Lean term that elaborates to `Prop` in the item’s context.

Hard rejections in the harness, before running Lean:

- Any top-level command keywords as standalone tokens:
  - `theorem`, `lemma`, `def`, `example`, `namespace`, `section`
- `by`
- `sorry`

Additional parsing rules:

- Accept multi-line terms.
- Strip markdown fences.
- Strip comments before scanning for forbidden tokens:
  - line comments `-- ...`
  - block comments `/- ... -/`
- Perform lexical, word-boundary checks for forbidden keywords.
- Treat the remaining text as the entire candidate term and let Lean decide whether it elaborates as a single term.

Optional strict mode:

- Reject `:=`
  - default off, since `let x := ...` can occur inside a `Prop` term

### 3.2 Per-attempt outcomes and buckets

For each attempt per item, record:

- Test 1: elaboration success of `def cand : Prop := <candidate>`
- Test 2: semantic check success

Bucket taxonomy:

- `output_parse_reject`
- `lean_parse_fail`
- `elab_fail`
- `shape_fail`
- `semantic_fail`
- `timeout`
- `pass`

### 3.3 Metrics

Compute at minimum:

- Well-formedness rate (Test 1 pass rate)
- Semantic rate (Test 2 pass rate)
- Combined rate (Test 1 and Test 2)
- Pass@k on combined rate

Recommended slices:

- by `family`
- by `tier`
- by `split`
- by top failure bucket

---

## 4) Repository structure

```text
.
├── dataset/
│   ├── schema.md
│   ├── pilot.jsonl
│   ├── dev.jsonl
│   ├── test.jsonl
│   ├── LICENSE_DATASET
│   └── provenance_notes.md
├── lean/
│   ├── lean-toolchain
│   ├── lakefile.lean
│   ├── AutoformalizationEval/
│   │   ├── Checks.lean
│   │   ├── Families/
│   │   │   ├── RingIdentity.lean
│   │   │   ├── FinTruthTable.lean
│   │   │   └── SetEquality.lean          (tier B later)
│   │   ├── Template/
│   │   │   ├── Test1.lean.template
│   │   │   └── Test2.lean.template
│   │   └── Version.lean
│   └── README.md
├── harness/
│   ├── pyproject.toml
│   ├── src/autoform_eval/
│   │   ├── cli.py
│   │   ├── dataset.py
│   │   ├── parse.py
│   │   ├── render.py
│   │   ├── lean_runner.py
│   │   ├── cache.py
│   │   ├── adapters/
│   │   │   ├── openai_adapter.py
│   │   │   └── gemini_adapter.py
│   │   ├── validate.py
│   │   ├── mutate.py
│   │   ├── report.py
│   │   └── types.py
│   └── README.md
├── docs/
│   ├── protocol.md
│   ├── threat_model.md
│   ├── add_item.md
│   └── families.md
├── results/
│   ├── baselines/                       (optional, or release artifacts)
│   └── README.md
├── .github/workflows/
│   ├── build_lean.yml
│   ├── validate_dataset.yml
│   └── tiny_eval.yml
├── .gitignore
├── LICENSE
├── CITATION.cff
└── README.md
```

---

## 5) Pinned Lean environment

### 5.1 Pin versions

- Commit `lean/lean-toolchain`
- Pin mathlib revision in `lean/lakefile.lean`

### 5.2 One-command setup

Provide documented commands such as:

- `make setup` or `./scripts/setup.sh`:
  - `cd lean && lake exe cache get` or equivalent
  - `cd lean && lake build`
  - `python -m pip install -e harness`

### 5.3 Determinism controls inside Lean

In the generated Lean files:

- `set_option autoImplicit false`
- `set_option maxHeartbeats <budget>`
- optionally `set_option maxRecDepth <budget>`

Use two budgets:

- smaller budget for Test 1
- larger budget for Test 2

---

## 6) Dataset schema v1

### 6.1 JSONL schema

Required fields:

- `schema_version` (string, for example `"1.0"`)
- `checker_version` (string, for example `"1.0"`)
- `id` (string)
- `nl` (string)
- `imports` (list of strings)
- `context` (string)
- `expected` (string, Lean `Prop` term)
- `family` (string)
- `tier` (`"A"` or `"B"`)
- `split` (`"pilot"`, `"dev"`, `"test"`)
- `tags` (list of strings)

Semantic fields:

- `semantic.kind` in `{ "normalized_ref", "decidable_ref", "behavioral" }`
- `semantic.check` (string key that names a reusable Lean checker)
- `semantic.extra` (optional string, per-item Lean snippet used only for behavioral checks)

Provenance:

- `provenance.source_kind` in `{ "mathlib_decl", "textbook", "competition", "other" }`
- `provenance.source_ref` (string, for mathlib use a fully qualified name or module)
- `provenance.license` (string, SPDX if possible)
- `provenance.notes` (optional string)

Optional escape hatch:

- `forbidden_ok` (optional list of strings)

### 6.2 Construction policy

- Prefer items where Test 2 is deterministic and does not depend on heavy proof search.
- Always include `expected`, even for behavioral items, so shape guard always runs.
- Avoid references that are tautologies or otherwise trivial in the intended domain.
- Keep contexts minimal and local.
- Use only public sources with clear licenses.
- Record provenance fields for every item.

---

## 7) Lean-side checker module

### 7.1 Public API surface

Create `AutoformalizationEval/Checks.lean` with:

- a shape guard
- extraction helpers
- a dispatch function keyed by `semantic.check`
- family-specific checkers under `AutoformalizationEval/Families/*`

Target stable API:

- `checkShape (family : String) (cand expected : Expr) : MetaM Unit`
- `checkFamily (checkKey : String) (cand expected : Expr) : MetaM Unit`

The checkers should fail with tagged errors so the harness can bucket failures reliably.

Error tag conventions:

- `[shape_fail] ...`
- `[semantic_fail] ...`

### 7.2 Shape guard rules

Run shape guard for every item as the first step of Test 2:

- Compare binder telescope length of `cand` and `expected`.
- Compare binder types up to definitional equality in order.
- Ignore binder names.
- Do not fail on binder implicitness differences in v1.
  - optionally record a warning later, but do not treat it as semantic failure.

Family-specific outer form constraints:

- equality family: the body head must be `Eq`
- inequality family: the body head must be `LT.lt` or `LE.le`
- set equality family: body must match the chosen set equality form

Fail fast with `[shape_fail]` messages that are short and consistent.

### 7.3 Family checker pattern

Each family checker follows:

1. Elaborate `cand` and `expected` as `Expr` of type `Prop`
2. Run `checkShape`
3. Canonicalize both into a comparable representation
4. Compare representations
5. On mismatch, throw `[semantic_fail] ...` with a short reason

### 7.4 Tier A families to implement first

#### A1) Ring and semiring identities, normalized reference comparison

Intended restricted form:

- `∀ x₁ ... xₙ, lhs = rhs` with `lhs`, `rhs` built from a restricted grammar

Checker approach:

- Extract binders, then extract `lhs`, `rhs` from both candidate and reference.
- Normalize `lhs` and `rhs` separately to a polynomial normal form.
- Compare normalized pairs, allowing symmetric swap of sides.

Design note:

- Compare pairs directly, do not rewrite as `lhs - rhs = 0`.

#### A2) Finite-domain truth table comparison

Intended restricted form:

- `∀ x₁ ... xₙ, φ` where all binders range over small decidable finite types
  - `Bool`, `Fin n` for small `n`, and small enums

Checker approach:

- Reify `φ` for both candidate and reference into a boolean evaluator.
- Enumerate all assignments.
- Compare full truth tables.
- If tables differ, fail with `[semantic_fail] truth_table_mismatch`.

Constraints:

- cap enumeration size per item using tags and validator checks
- store the cap in the item tags, for example `enum_cap:256`

### 7.5 Tier B families to implement after Tier A stabilizes

#### B1) Set equalities with deterministic canonicalization

Approach:

- normalize both sides using a curated simp set
- apply extensionality in a fixed pattern
- reduce to a canonical boolean normal form if feasible
- compare canonicalized expressions

Strict constraints:

- limit the allowed constructs in the set expressions
- treat anything outside the fragment as an item design bug

#### B2) Linear arithmetic inequalities with tight constraints

Only include cases where the check is stable under a deterministic normalizer for the fragment.
Avoid broad “let a tactic solve it” checks.

### 7.6 Behavioral checks with mandatory anti-test

For `semantic.kind = behavioral`:

- Always run shape guard first.
- Then run 1 to 3 “must hold” consequences.
- Then run at least 1 anti-test that rejects vacuous or overly strong candidates.

Keep snippets short and deterministic with tight heartbeat budgets.

---

## 8) Lean templates and execution model

### 8.1 Standardized template files

Store two templates:

- `Test1.lean.template`
  - imports
  - context
  - `def cand : Prop := <CAND>`
  - minimal compile target

- `Test2.lean.template`
  - same imports and context
  - `def cand : Prop := <CAND>`
  - `def expected : Prop := <EXPECTED>`
  - `theorem test2_ok : True := by`
    - call checker dispatch using `semantic.check`
    - `trivial`

### 8.2 Two-stage execution

Harness flow per attempt:

1. Render and run Test 1 with:

- short wall-clock timeout
- small heartbeat budget

2. If Test 1 passes, render and run Test 2 with:

- longer wall-clock timeout
- larger heartbeat budget

This yields clean attribution for:

- parse failures
- elaboration failures
- shape failures
- semantic failures
- timeouts

---

## 9) Dataset validation tooling

### 9.1 Validator goals

The validator must ensure:

- schema correctness and required fields
- Lean compilation and deterministic runtime budget
- semantic strength, not just compilation success
- absence of forbidden tokens in dataset fields
- provenance completeness

### 9.2 Validator checks per item

For each item:

1. Schema validation

- validate required fields
- validate allowed values for family, tier, split, semantic.kind
- validate versions

2. Static text checks

- scan `context`, `expected`, and `semantic.extra` for forbidden tokens
- allow only whitelisted exceptions via `forbidden_ok`

3. Compilation self-check

- run Test 1 with `cand := expected`, must pass
- run Test 2 with `cand := expected`, must pass

4. Mutation tests
   Generate 1 to 3 wrong-but-well-formed mutants and ensure Test 2 rejects them.

Examples:

- ring identity: replace the first `+` with `*`, or replace a numeral, or apply `^ 2` to one side
- finite truth table: wrap body in `Not`, or flip one atom `=` to `≠`

Requirements:

- mutant must still elaborate as `Prop`
- at least one mutant must fail shape or semantic

If mutants pass, mark the item invalid until strengthened.

5. Determinism and budget checks

- record elapsed time
- enforce heartbeat caps
- fail if over budget

### 9.3 Validator outputs

Write:

- `dataset/validation_report.json` with per-item status and timings
- optional `dataset/expected_hashes.json` with:
  - expected shape hash
  - expected canonical hash for families that support it

---

## 10) Harness implementation

### 10.1 CLI commands

Provide a single CLI with subcommands, for example:

- `autoform-eval validate --split pilot`
- `autoform-eval run --models openai,gemini --split pilot --k 1 --config configs/baseline.yaml`
- `autoform-eval report --run results/runs/<run_id>`

### 10.2 Core runner flow

Per item per attempt:

1. Build prompt

- include `nl`
- include a compact summary of context declarations if available
- include output rules
- include 2 to 3 examples of valid outputs for similar style

2. Call model adapter

- stable request settings from config
- retries with backoff on transient errors

3. Parse output

- strip fences
- strip comments
- lexical forbidden token scan
- pass through as single candidate string

4. Run Lean Test 1

- render template
- execute `lake env lean` with timeout and heartbeat options

5. If Test 1 passes, run Lean Test 2

- same approach with semantic checker

6. Classify bucket

- map Lean exit code and error tags to buckets
- store stderr excerpt and full logs

7. Save artifacts

- raw candidate text
- rendered Lean files
- stdout, stderr
- metadata record in results.jsonl

### 10.3 Output parsing specifics

Implementation requirements:

- Do not enforce “single line”.
- Do enforce “single term” by letting Lean parse at the insertion site.
- Reject multiple outputs only when they represent multiple candidates.
  - for v1, simplest rule is: allow newlines, but do not allow multiple top-level code blocks
  - rely on Lean parsing to reject extra tokens

### 10.4 Caching

Cache model outputs by hash of:

- adapter name
- model name
- decoding params
- prompt text
- item id
- schema_version and checker_version

Cache Lean outcomes by hash of:

- rendered Lean file contents
- Lean toolchain string
- mathlib revision
- heartbeat budget settings

Cache directory structure:

- `harness_cache/model/<hash>.json`
- `harness_cache/lean/<hash>.json`

### 10.5 Security hygiene

- Read API keys from environment variables only.
- `.env` in `.gitignore`.
- Never print keys in logs.
- CI secrets guard:
  - scan committed files for common key patterns
  - fail fast

---

## 11) Results and reporting

### 11.1 Results artifacts

Write per run:

- `results.jsonl`
- `summary.json`
- `report.md`
- `logs/` directory with per-item logs
- `rendered/` directory with Lean files for failures

### 11.2 results.jsonl record shape

Include:

- identifiers
  - `run_id`
  - `item_id`
  - `split`
  - `family`
  - `tier`
  - `tags`
- model info
  - `provider` (`openai` or `gemini`)
  - `model`
  - `params`
- prompt info
  - `prompt_hash`
  - optional `prompt_text` if configured
- candidate info
  - `candidate_raw`
  - `candidate_hash`
- Lean environment
  - `lean_toolchain`
  - `mathlib_rev`
  - `test1_heartbeats`
  - `test2_heartbeats`
- outcomes
  - `test1_pass`
  - `test2_pass`
  - `shape_pass` (if distinguishable)
  - `bucket`
- timing
  - `test1_elapsed_ms`
  - `test2_elapsed_ms`
- logs
  - `stderr_excerpt`
  - `stdout_excerpt`
  - file paths for full logs

### 11.3 summary.json metrics

Compute:

- overall Test 1 rate, Test 2 rate, combined rate
- Pass@k combined
- breakdown by family
- breakdown by tier
- breakdown by bucket

### 11.4 report.md contents

Include:

- a main table by model
- tier and family slices
- top failure buckets and examples
- 5 to 10 qualitative examples per model:
  - NL statement
  - reference proposition
  - candidate output
  - bucket and key Lean error excerpt

---

## 12) CI workflow

### 12.1 build_lean job

- cache lake build artifacts
- run `lake build` in pinned environment
- fail on any build error

### 12.2 validate_dataset job

- run schema validation
- run compilation self-checks
- run mutation tests
- enforce budgets and determinism

### 12.3 tiny_eval job

- runs a tiny subset with:
  - cached model outputs, or
  - a mock adapter that returns known candidates
- ensures end-to-end harness still works

### 12.4 secrets guard job

- scan for key patterns
- fail if suspected secrets are committed

---

## 13) Documentation package

### 13.1 Top-level README

Must include:

- what is measured and what is not
- overview of Test 1 and Test 2
- why trivial outputs do not pass:
  - output contract hard rejections
  - shape guard
  - family checks
  - behavioral anti-tests
  - mutation tests in validator
- reproduction steps from scratch
- pinned versions and how to verify them
- how to cite the benchmark

### 13.2 docs/protocol.md

- fixed baseline protocol and config format
- all default settings
- how to add models
- how to run Pass@k

### 13.3 docs/threat_model.md

- known ways models might try to game the harness
- defenses in v1
- limitations that remain

### 13.4 docs/add_item.md

- schema template
- examples for each semantic.kind
- rules for choosing tier
- how to add provenance
- common mistakes and how validator catches them

---

## 14) Milestones and acceptance criteria

### Milestone 1: End-to-end pilot

Deliverables:

- `dataset/pilot.jsonl` with ~30 items
  - 5 families × 6 items is a good target
  - majority Tier A
  - provenance fields filled
- `AutoformalizationEval/Checks.lean` with:
  - shape guard
  - dispatch by `semantic.check`
  - at least 2 Tier A family checkers:
    - ring identity canonicalization
    - finite-domain truth table comparison
- harness supports:
  - OpenAI adapter
  - Gemini adapter
  - caching and artifact writing
- reporting produces:
  - `results.jsonl`
  - `summary.json`
  - `report.md`
- CI runs:
  - build_lean
  - validate_dataset with mutation tests
  - tiny_eval
  - secrets guard

Acceptance criteria:

- all pilot items validate in CI
- the pilot evaluation is reproducible from scratch following README
- buckets are clean, stable, and informative

### Milestone 2: Scale dataset and strengthen families

Deliverables:

- expand to larger dev and test splits
- dedup and leakage checks
- tier tags used in reports
- stable timeouts and heartbeat budgets

Acceptance criteria:

- validator passes on full dataset
- semantic checks stay within strict budget
- minimal flakiness across reruns

### Milestone 3: Baselines on frontier models

Deliverables:

- fixed baseline protocol config committed
- baseline outputs published as release artifacts or committed results
- analysis and failure mode breakdown

Acceptance criteria:

- baselines regenerable with cached outputs and pinned environment
- report identifies dominant failure modes per model

### Milestone 4: Public release package

Deliverables:

- versioned dataset release
- harness tag release
- license and provenance notes complete
- short technical note scaffold

Acceptance criteria:

- an external reader can run it with minimal friction
- results are interpretable and reproducible

---

## 15) Recommended initial item families for v1

Prioritize deterministic Tier A families first:

1. Ring and semiring identities with normalized pairwise comparison
2. Finite-domain truth table equivalence for Bool and small Fin domains
3. Boolean small-structure properties via enumeration
4. Set equalities in a restricted fragment as Tier B after stability
5. Linear inequality fragment as Tier B only under strict constraints

Pilot mix recommendation:

- 70 to 90 percent Tier A
- 10 to 30 percent Tier B only after Tier A pipeline is stable

---

## 16) Concrete first milestone checklist

- Dataset
  - [ ] 30 pilot items
  - [ ] provenance and license fields filled
  - [ ] mutation tests pass per item

- Lean
  - [ ] shape guard implemented
  - [ ] ring identity checker implemented
  - [ ] finite truth table checker implemented
  - [ ] tagged error messages `[shape_fail]` and `[semantic_fail]`

- Harness
  - [ ] adapters for OpenAI and Gemini
  - [ ] caching
  - [ ] two-stage Lean execution with timeouts and heartbeats
  - [ ] results.jsonl, summary.json, report.md generation

- CI
  - [ ] build_lean
  - [ ] validate_dataset
  - [ ] tiny_eval
  - [ ] secrets guard

This plan produces a v1 that is defensible, deterministic, and extensible, with CI enforcing semantic strength rather than just compilation.

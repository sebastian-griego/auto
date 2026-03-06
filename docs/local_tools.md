# Local Lean Tools

This repository includes local-only Lean tooling accessible through Python wrappers and `autoform_eval.cli tools`.

## Tools

### `check`
- Compiles full Lean content and returns structured status.
- Input is full Lean content (module-level commands/decls allowed).

### `verify-proof`
- Verifies candidate declaration snippets against formal spec declaration snippets.
- Wrapped under:
  - `namespace Spec ... end Spec`
  - `namespace Cand ... end Cand`
- Checks declaration presence, kind compatibility, type defeq, and selected value defeq (`def`/`opaque` when applicable).
- Scans candidate declarations for `sorryAx` and supports `permitted_sorries` suffix allowlists.
- Result payload includes declaration inventories: `spec_declarations` and `candidate_declarations`.

### `extract-theorems`
- Extracts theorem metadata from declaration snippets wrapped under `namespace ExtractTmp`.
- Returns theorem name/type, `is_sorry`, and local/external dependencies.

### `inspect-prop`
- Inspects a single Prop snippet wrapped as:
  - `namespace InspectTmp`
  - `def target : Prop := <prop>`
  - `end InspectTmp`
- Returns pretty-printed expression/type/whnf, leading-forall metadata, `contains_sorry`, and local/external dependencies.

## Imports and Preamble

- All tools accept repeated `--import MODULE` (Python: `imports=[...]`).
- `verify-proof`, `extract-theorems`, and `inspect-prop` default to `Mathlib` when imports are omitted.
- `verify-proof`, `extract-theorems`, and `inspect-prop` accept optional preambles (`--preamble PATH` / `preamble=...`).
- Preamble is inserted after imports and before wrapper namespaces, and is **not** wrapped inside `Spec`/`Cand`/`ExtractTmp`/`InspectTmp`.

## Cache Behavior

Cache directories (under `harness_cache/`):
- `lean_tools_sources/`: generated `.lean` source files
- `lean_tools_results/`: cached JSON result entries

Stable cache keys include:
- tool name
- imports
- payload/snippets (including preamble where applicable)
- pinned Lean files (`lean/lean-toolchain`, `lean/lakefile.lean`)
- tool source fingerprints (`lean_tools.py`, `Tools/Common.lean`, `Tools/VerifyProof.lean`, `Tools/ExtractTheorems.lean`, `Tools/InspectProp.lean`)
- local `TOOLS_SCHEMA_VERSION`

`timeout_seconds` is intentionally excluded from the cache key.

Every tool result includes:
- `cache_key`: stable hash key used for cache/source naming
- `source_path`: generated Lean source path
- `cached`: whether result was returned from result cache

Use `--no-cache` (or `use_cache=False`) to bypass result cache reads/writes while still writing source files.

## Internal Name Filtering

User-facing declaration/dependency outputs filter internal compiler-generated names (aux/internal details) using Lean name predicates, so helper internals (for example match/proof aux names) are omitted from tool outputs.

## CLI Examples

```bash
python -m autoform_eval.cli tools check \
  --content /tmp/check_input.lean \
  --import Init \
  --no-cache
```

```bash
python -m autoform_eval.cli tools verify-proof \
  --formal /tmp/formal_snippet.lean \
  --content /tmp/candidate_snippet.lean \
  --import Mathlib \
  --preamble /tmp/preamble.lean \
  --permitted-sorries helper,Sub.helper
```

```bash
python -m autoform_eval.cli tools extract-theorems \
  --content /tmp/declarations.lean \
  --import Mathlib \
  --preamble /tmp/preamble.lean
```

```bash
python -m autoform_eval.cli tools inspect-prop \
  --prop /tmp/prop_snippet.lean \
  --import Mathlib \
  --preamble /tmp/preamble.lean
```

## Python API

```python
from autoform_eval.lean_tools import (
    check_content,
    verify_proof,
    extract_theorems,
    inspect_prop,
)

check_content(content, imports=["Init"], use_cache=False)
verify_proof(formal_statement, content, imports=["Mathlib"], preamble=preamble, use_cache=True)
extract_theorems(content, imports=["Mathlib"], preamble=preamble)
inspect_prop(prop, imports=["Mathlib"], preamble=preamble)
```

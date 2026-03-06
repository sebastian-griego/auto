# Local Lean Tools

This repository includes local-only Lean tooling accessible through Python and CLI wrappers.

## Tools

### `check`
- Compiles full Lean content and reports structured status.
- Input is a full Lean module snippet (commands/decls are allowed).

### `verify-proof`
- Verifies candidate declarations against a formal spec snippet.
- `Spec.<suffix>` declarations must be implemented by matching `Cand.<suffix>` declarations.
- Compares declaration kind + type (and value for `def`/`opaque` when applicable).
- Scans all candidate declarations for `sorryAx` usage.

### `extract-theorems`
- Extracts theorem metadata from a declaration snippet.
- Returns theorem name, type, `is_sorry`, and local/external dependency lists for theorem type/proof expressions.

## Snippet Contracts

### `verify-proof`
- `--formal` and `--content` are declaration snippets, not full modules.
- Wrapping performed by the tool:
  - `namespace Spec ... end Spec`
  - `namespace Cand ... end Cand`

### `extract-theorems`
- `--content` is a declaration snippet, not a full module.
- Wrapping performed by the tool:
  - `namespace ExtractTmp ... end ExtractTmp`

### `check`
- Accepts full Lean content directly.
- Optional `--import` modules are prepended before the content.

## Imports

- All tools accept repeated `--import MODULE`.
- `verify-proof` and `extract-theorems` default to `Mathlib` when no import is provided.

## Permitted Sorries

`verify-proof` supports `--permitted-sorries` with candidate-relative suffixes:
- Example: `helper,Sub.helper`
- These are interpreted under `Cand` and allow `sorryAx` only for those candidate declarations.

## Cache Layout

Under `harness_cache/`:
- `lean_tools_sources/`: generated `.lean` tool files keyed by stable content hash
- `lean_tools_results/`: cached JSON results keyed by stable content hash

Stable keys include tool name, imports, snippets, permitted sorries, and pinned Lean config file contents (`lean/lean-toolchain`, `lean/lakefile.lean`).

## Example Commands

```bash
python -m autoform_eval.cli tools check \
  --content /tmp/check_input.lean \
  --import Init
```

```bash
python -m autoform_eval.cli tools verify-proof \
  --formal /tmp/formal_snippet.lean \
  --content /tmp/candidate_snippet.lean \
  --import Mathlib \
  --permitted-sorries helper,Sub.helper
```

```bash
python -m autoform_eval.cli tools extract-theorems \
  --content /tmp/declarations.lean \
  --import Mathlib
```

## Python API

```python
from autoform_eval.lean_tools import check_content, verify_proof, extract_theorems

check_content(content, imports=["Init"])
verify_proof(formal_statement, content, imports=["Mathlib"], permitted_sorries=["helper"])
extract_theorems(content, imports=["Mathlib"])
```

# Dataset Schema v1.0

Split files are JSONL encoded as UTF-8, with or without a BOM. Each row must
have a unique `id` within its split file; duplicate IDs are rejected before
validation or evaluation runs proceed.

Required fields per JSONL row:
- `schema_version` (string)
- `checker_version` (string)
- `id` (string)
- `nl` (string)
- `imports` (list[string])
- `context` (string)
- `expected` (string)
- `family` (string)
- `tier` (`A` or `B`)
- `split` (`pilot`, `dev`, `test`)
- `tags` (list[string])

Required nested fields:
- `semantic.kind` (`normalized_ref`, `decidable_ref`, `behavioral`)
- `semantic.check` (string)

Optional nested fields:
- `semantic.extra` (string when present)

Required provenance fields:
- `provenance.source_kind` (`mathlib_decl`, `textbook`, `competition`, `assistant_generated`, `other`)
- `provenance.source_ref` (string)
- `provenance.license` (string)

Optional fields:
- `provenance.notes` (string when present)
- `forbidden_ok` (list[string] when present)

# Dataset Schema v1.0

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
- `semantic.extra` (string)

Required provenance fields:
- `provenance.source_kind` (`mathlib_decl`, `textbook`, `competition`, `other`)
- `provenance.source_ref` (string)
- `provenance.license` (string)

Optional fields:
- `provenance.notes` (string)
- `forbidden_ok` (list[string])

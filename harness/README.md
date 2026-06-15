# Harness

CLI entrypoint:

```bash
python -m autoform_eval.cli --help
```

Key subcommands:
- `validate`: dataset schema/static checks plus optional Lean self-checks
- `run`: model evaluation run with artifacts
- `report`: rebuild summary/report from `results.jsonl`
- `verify-manifest`: verify hashes in a generated `manifest.json`

Useful options:
- `run --k <N>` for Pass@k attempts per item/model.
- `run --save-prompt-text` to persist prompt text in records.
- `run --prompt-version <version>` to pin benchmark prompt text (default `v1.0.0`).
- `run --provider-retries <N> --provider-retry-backoff-s <seconds>` to retry transient provider failures.
- `validate --determinism-repeats <N> [--determinism-jitter-ms <ms>]` for rerun stability checks.

Notes:
- Provider/API failures are tracked as `provider_error` buckets.
- Transient provider errors are retried and are not cached as sticky failures.
- Summary rates are computed on evaluable attempts (provider errors excluded from denominators).
- `report` validates saved `results.jsonl` artifacts and rejects malformed buckets,
  non-boolean pass flags, impossible pass-state combinations, invalid attempt
  indexes, malformed optional artifact fields, and duplicate attempt rows.
- `run` and `report` write `manifest.json` with SHA-256 hashes for core run
  artifacts and any referenced rendered/log files that are present. `run`
  requires referenced rendered/log files to exist before the manifest is written.
- `verify-manifest` is strict by default: it rejects modified, missing, or
  unlisted files in a run directory, and it fails when `manifest.json` records
  missing rendered/log artifacts. It reloads `results.jsonl` to validate row
  shape, run ID scope, attempt counts, `summary.json` consistency, and
  referenced artifact accounting. Use `--allow-missing-record-artifacts` and
  `--allow-extra-artifacts` only for older partial archives.

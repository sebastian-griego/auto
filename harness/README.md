# Harness

CLI entrypoint:

```bash
python -m autoform_eval.cli --help
```

Key subcommands:
- `validate`: dataset schema/static checks plus optional Lean self-checks
- `run`: model evaluation run with artifacts
- `report`: rebuild summary/report from `results.jsonl`

Useful options:
- `run --k <N>` for Pass@k attempts per item/model.
- `run --save-prompt-text` to persist prompt text in records.
- `run --prompt-version <version>` to pin benchmark prompt text (default `v1.0.0`).
- `validate --determinism-repeats <N> [--determinism-jitter-ms <ms>]` for rerun stability checks.

Notes:
- Provider/API failures are tracked as `provider_error` buckets.
- Summary rates are computed on evaluable attempts (provider errors excluded from denominators).

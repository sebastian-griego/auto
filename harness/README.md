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
- `validate --determinism-repeats <N> [--determinism-jitter-ms <ms>]` for rerun stability checks.

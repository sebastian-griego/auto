# Baseline Protocol (v1 bootstrap)

## Fixed defaults
- `k = 1`
- `temperature = 0.0`
- Test1 heartbeats: `40000`
- Test2 heartbeats: `200000`
- Test1 timeout: `8s`
- Test2 timeout: `20s`
- Validate budget defaults:
  - `budget1_ms = timeout1 * 1000`
  - `budget2_ms = timeout2 * 1000`

## Run command
```bash
cd harness
python -m autoform_eval.cli run \
  --split pilot \
  --models openai:gpt-5,gemini:gemini-2.5-pro \
  --k 1
```

## Pass@k
Use `--k <int>`. `summary.json` now reports deterministic `pass_at_k.rates`
per model and overall, grouped by `(provider, model, item_id)`.

Example:
```bash
cd harness
python -m autoform_eval.cli run --split pilot --models openai:gpt-5 --k 3
```

Optional:
- `--save-prompt-text` records raw prompt text in `results.jsonl`.

## Validator budgets
Example:
```bash
cd harness
python -m autoform_eval.cli validate --split pilot --budget1-ms 6000 --budget2-ms 12000
```

## Determinism reruns
The validator can rerun Test2 per item to check deterministic outcomes:

```bash
cd harness
python -m autoform_eval.cli validate \
  --split pilot \
  --determinism-repeats 2 \
  --determinism-jitter-ms 3000
```

- `--determinism-repeats`: number of Test2 reruns per item (>= 1).
- `--determinism-jitter-ms`: optional elapsed-time jitter cap across reruns.

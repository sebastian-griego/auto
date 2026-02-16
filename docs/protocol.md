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
Use `--k <int>` and aggregate combined pass in `summary.json`.

## Validator budgets
Example:
```bash
cd harness
python -m autoform_eval.cli validate --split pilot --budget1-ms 6000 --budget2-ms 12000
```

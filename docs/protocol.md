# Baseline Protocol (v1 bootstrap)

## Fixed defaults
- `k = 1`
- `temperature = 0.0`
- `prompt_version = v1.1.0`
- Test1 heartbeats: `40000`
- Test2 heartbeats: `200000`
- Test1 timeout: `8s`
- Test2 timeout: `20s`
- Validate budget defaults:
  - `budget1_ms = timeout1 * 1000`
  - `budget2_ms = timeout2 * 1000`

## Benchmark prompt
- Prompt text is versioned in code at `harness/src/autoform_eval/prompt.py`.
- Run artifacts include `prompt_version`, `prompt_hash`, and optional `prompt_text`.
- If prompt text changes, bump `BENCHMARK_PROMPT_VERSION` and treat results as a new baseline.
- Frozen v1 reruns should explicitly pass `--prompt-version v1.0.0`.

## Run command (reproducible local)
```bash
cd harness
python -m autoform_eval.cli run \
  --split pilot \
  --models openai:mock \
  --mock \
  --k 1 \
  --prompt-version v1.1.0
```

## Run command (real providers)
Provider/model availability is account-dependent. Unavailable models are bucketed as `provider_error`
and excluded from semantic-rate denominators.

```bash
cd harness
python -m autoform_eval.cli run \
  --split pilot \
  --models openai:gpt-4.1-mini,gemini:gemini-2.5-pro \
  --k 1 \
  --prompt-version v1.1.0
```

## Pass@k
Use `--k <int>`. `summary.json` now reports deterministic `pass_at_k.rates`
per model and overall, grouped by `(provider, model, item_id)`.

Example:
```bash
cd harness
python -m autoform_eval.cli run --split pilot --models openai:gpt-4.1-mini --k 3
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

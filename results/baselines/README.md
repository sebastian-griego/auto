# Baseline Artifacts

`results/runs/` is ignored by git, so baseline artifacts that should be reviewed or published must be copied under `results/baselines/`.

## Reproduce real provider pilot baselines

```bash
python -m pip install -e "harness[openai,gemini]"
export OPENAI_API_KEY='...'
export GEMINI_API_KEY='...'

cd harness
python -m autoform_eval.cli run \
  --split pilot \
  --models openai:gpt-5,gemini:gemini-2.5-pro \
  --k 1

python -m autoform_eval.cli run \
  --split pilot \
  --models openai:gpt-5,gemini:gemini-2.5-pro \
  --k 3
```

## Promote a run into tracked artifacts

Replace `RUN_ID` with the printed run id:

```bash
RUN_ID=YYYYMMDD_HHMMSS

mkdir -p results/baselines/pilot/$RUN_ID
cp results/runs/$RUN_ID/results.jsonl results/baselines/pilot/$RUN_ID/
cp results/runs/$RUN_ID/summary.json results/baselines/pilot/$RUN_ID/
cp results/runs/$RUN_ID/report.md results/baselines/pilot/$RUN_ID/
```

Add baseline metadata:

```bash
cat > results/baselines/pilot/$RUN_ID/METADATA.txt <<'EOF'
split=pilot
k=<1_or_3>
temperature=0.0
max_output_tokens=512
lean_toolchain=see lean/lean-toolchain
mathlib_rev=see lean/lakefile.lean
EOF
```

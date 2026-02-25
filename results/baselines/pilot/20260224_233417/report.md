# Autoformalization Eval Report

## Overall

- Total attempts: 15
- Evaluable attempts (exclude provider errors): 15
- Provider error attempts: 0
- Provider error rate: 0.000
- Test1 rate (evaluable only): 1.000
- Test2 rate (evaluable only): 0.933
- Combined rate (evaluable only): 0.933
- Pass@1 (evaluable only): 0.933

## Model Table

| Model | Attempts | Evaluable | ProviderErr | Items | Test1 | Test2 | Combined | Pass@k(max) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| gemini:gemini-2.5-pro | 15 | 15 | 0 | 15 | 1.000 | 0.933 | 0.933 | 0.933 |

## Family Slice

- fin_truth_table: total=8 combined=0.875
- ring_identity: total=7 combined=1.000

## Tier Slice

- A: total=15 combined=0.933

## Buckets

- pass: 14
- semantic_fail: 1

## Sample failures

- item `ftt_pilot_0006` bucket `semantic_fail`
  - candidate: `forall (a b : Bool), (a = b) = (a = true ↔ b = true)`
  - lean_output: `/home/jovyan/auto/results/runs/20260224_233417/rendered/ftt_pilot_0006.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] truth_table_mismatch:a := false, b := true`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260224_233417/rendered/ftt_pilot_0006.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] truth_table_mismatch:a := false, b := true`

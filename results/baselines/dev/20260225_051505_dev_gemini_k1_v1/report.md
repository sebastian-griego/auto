# Autoformalization Eval Report

## Overall

- Total attempts: 100
- Evaluable attempts (exclude provider errors): 100
- Provider error attempts: 0
- Provider error rate: 0.000
- Test1 rate (evaluable only): 1.000
- Test2 rate (evaluable only): 0.830
- Combined rate (evaluable only): 0.830
- Pass@1 (evaluable only): 0.830

## Model Table

| Model | Attempts | Evaluable | ProviderErr | Items | Test1 | Test2 | Combined | Pass@k(max) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| gemini:gemini-2.5-pro | 100 | 100 | 0 | 100 | 1.000 | 0.830 | 0.830 | 0.830 |

## Family Slice

- fin_truth_table: total=60 combined=0.917
- ring_identity: total=40 combined=0.700

## Tier Slice

- A: total=100 combined=0.830

## Buckets

- pass: 83
- semantic_fail: 12
- shape_fail: 5

## Sample failures

- item `ftt_dev_0011` bucket `shape_fail`
  - candidate: `forall (a b : Bool), a ≠ b`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ftt_dev_0011.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [shape_fail] binder_arity`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ftt_dev_0011.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [shape_fail] binder_arity`
- item `ftt_dev_0014` bucket `shape_fail`
  - candidate: `forall (a b c : Bool), (a = true ∧ b = true) → c = true`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ftt_dev_0014.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [shape_fail] binder_arity`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ftt_dev_0014.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [shape_fail] binder_arity`
- item `ftt_dev_0031` bucket `shape_fail`
  - candidate: `forall (a : Bool) (b : Bool) (c : Bool), (a = true ∧ b = true ∧ c = true) → (a = true ∧ b = true ∧ c = true)`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ftt_dev_0031.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [shape_fail] binder_arity`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ftt_dev_0031.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [shape_fail] binder_arity`
- item `ftt_dev_0034` bucket `shape_fail`
  - candidate: `forall (a b c : Bool), (a = true ∧ b = true) → c = true`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ftt_dev_0034.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [shape_fail] binder_arity`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ftt_dev_0034.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [shape_fail] binder_arity`
- item `ftt_dev_0063` bucket `shape_fail`
  - candidate: `forall (a : Bool) (c : Enum_ftt_dev_0063), (a = false ∧ c = Enum_ftt_dev_0063.sun) → (a = false ∧ c = Enum_ftt_dev_0063.`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ftt_dev_0063.gemini.gemini-2.5-pro.k1.test2.lean:19:0: error: [shape_fail] binder_arity`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ftt_dev_0063.gemini.gemini-2.5-pro.k1.test2.lean:19:0: error: [shape_fail] binder_arity`
- item `ring_dev_0018` bucket `semantic_fail`
  - candidate: `forall (e a d : R), (e + a) * ((d + 1) * (e * 1 + (a + 1))) = e * (d * (e * 1)) + e * (d * (a + 1)) + e * (1 * (e * 1)) `
  - lean_output: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ring_dev_0018.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch cand_`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ring_dev_0018.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch cand_`
- item `ring_dev_0019` bucket `semantic_fail`
  - candidate: `forall (e b d : R), (((1 + e) + (e + b)) * (e * d)) = (((1 * (e * d)) + (e * (e * d))) + ((e * (e * d)) + (b * (e * d)))`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ring_dev_0019.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch cand_`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ring_dev_0019.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch cand_`
- item `ring_dev_0024` bucket `semantic_fail`
  - candidate: `forall (e a c d : R), (((e + 1) + (a + c)) * (a * d)) = (((e + 1) * (a * d)) + ((a + c) * (a * d)))`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ring_dev_0024.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch cand_`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ring_dev_0024.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch cand_`
- item `ring_dev_0025` bucket `semantic_fail`
  - candidate: `forall (c a e : R), (((c + a) + (a * e)) * (a + e)) = (((c + a) * a) + ((c + a) * e)) + (((a * e) * a) + ((a * e) * e))`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ring_dev_0025.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch cand_`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ring_dev_0025.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch cand_`
- item `ring_dev_0028` bucket `semantic_fail`
  - candidate: `forall (e a c d : R), ((((e * a) + (a + c)) * (a * d)) + (((e * a) + (a + c)) * (e + c))) = (((e * a) + (a + c)) * ((a *`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ring_dev_0028.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch cand_`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_051505_dev_gemini_k1_v1/rendered/ring_dev_0028.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch cand_`

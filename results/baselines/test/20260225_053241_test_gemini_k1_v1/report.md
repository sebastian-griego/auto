# Autoformalization Eval Report

## Overall

- Total attempts: 200
- Evaluable attempts (exclude provider errors): 199
- Provider error attempts: 1
- Provider error rate: 0.005
- Test1 rate (evaluable only): 1.000
- Test2 rate (evaluable only): 0.899
- Combined rate (evaluable only): 0.899
- Pass@1 (evaluable only): 0.899

## Model Table

| Model | Attempts | Evaluable | ProviderErr | Items | Test1 | Test2 | Combined | Pass@k(max) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| gemini:gemini-2.5-pro | 200 | 199 | 1 | 200 | 1.000 | 0.899 | 0.899 | 0.899 |

## Family Slice

- fin_truth_table: total=137 combined=0.985
- ring_identity: total=62 combined=0.710

## Tier Slice

- A: total=199 combined=0.899

## Buckets

- pass: 179
- provider_error: 1
- semantic_fail: 19
- shape_fail: 1

## Sample failures

- item `ftt_test_0018` bucket `semantic_fail`
  - candidate: `forall (a b : Bool), a && b = false`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ftt_test_0018.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] truth_table_mismatch:a := f`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ftt_test_0018.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] truth_table_mismatch:a := f`
- item `ftt_test_0019` bucket `semantic_fail`
  - candidate: `forall (a b : Bool), a || b = false`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ftt_test_0019.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] truth_table_mismatch:a := t`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ftt_test_0019.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] truth_table_mismatch:a := t`
- item `ring_test_0016` bucket `semantic_fail`
  - candidate: `forall (a b c d : R), (b + c + d) * a = b * a + c * a + d * a`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ring_test_0016.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch can`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ring_test_0016.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch can`
- item `ftt_test_0040` bucket `provider_error`
  - candidate: ``
  - lean_output: `provider_error:ConnectError:[Errno -3] Temporary failure in name resolution`
  - stderr_excerpt: `provider_error:ConnectError:[Errno -3] Temporary failure in name resolution`
  - stdout_excerpt: ``
- item `ring_test_0027` bucket `semantic_fail`
  - candidate: `forall (e b a d : R), (e + b) * (e * b * (b * a + (d + b))) = e * (e * b * (b * a + (d + b))) + b * (e * b * (b * a + (d`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ring_test_0027.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch can`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ring_test_0027.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch can`
- item `ring_test_0029` bucket `semantic_fail`
  - candidate: `forall (e c d : R), (((e + c) * (e + 1)) + ((c * d) * (e + 1))) = (((e + c) + (c * d)) * (e + 1))`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ring_test_0029.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch can`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ring_test_0029.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch can`
- item `ring_test_0030` bucket `semantic_fail`
  - candidate: `forall (e b d : R), (((e + b) * e) + ((e + b) * (d + b))) = ((e + b) * (e + (d + b)))`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ring_test_0030.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch can`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ring_test_0030.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch can`
- item `ring_test_0032` bucket `semantic_fail`
  - candidate: `forall (e a d c : R), ((((1 + e) + (a + d)) * (1 + c)) + (((1 + e) + (a + d)) * (a * 1))) = (((1 + e) + (a + d)) * ((1 +`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ring_test_0032.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch can`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ring_test_0032.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch can`
- item `ring_test_0033` bucket `semantic_fail`
  - candidate: `forall (c a e : R), (((c + a) + (e * a)) * (c * 1)) * (a + 1) = (((c + a) * (c * 1)) + ((e * a) * (c * 1))) * a + (((c +`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ring_test_0033.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch can`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ring_test_0033.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch can`
- item `ring_test_0038` bucket `semantic_fail`
  - candidate: `forall (e a b : R), (((e + a) + (e * 1)) * (a + b)) + (((e + a) + (e * 1)) * b) = (((e + a) + (e * 1)) * ((a + b) + b))`
  - lean_output: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ring_test_0038.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch can`
  - stderr_excerpt: ``
  - stdout_excerpt: `/home/jovyan/auto/results/runs/20260225_053241_test_gemini_k1_v1/rendered/ring_test_0038.gemini.gemini-2.5-pro.k1.test2.lean:15:0: error: [semantic_fail] ring_identity_mismatch can`

# v1 Baseline Results

This report summarizes the frozen v1 benchmark baselines (Gemini, `k=1`, prompt `v1.0.0`).

See also: `docs/v1_freeze.md` and tag `v1-freeze-20260225`.

## Dataset Sizes

| Split | Total | fin_truth_table | ring_identity |
|---|---:|---:|---:|
| pilot | 15 | 8 | 7 |
| dev | 100 | 60 | 40 |
| test | 200 | 138 | 62 |

## Metric Definitions

- `Test1`: candidate elaborates as `Prop` (`def cand : Prop := ...` succeeds).
- `Test2`: candidate passes shape guard plus deterministic family semantic check.
- `Combined rate`: `Test1 && Test2` over evaluable attempts.
- `Pass@k`: item-level pass over up to `k` attempts; here `k=1`.
- `provider_error` attempts are excluded from success-rate denominators and reported separately.

## Baseline Runs (Gemini, k=1)

| Split | Run ID | Attempts | Evaluable | ProviderErr | Test1 | Test2 | Combined | Pass@1 |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| pilot | `20260224_233417` | 15 | 15 | 0 | 1.000 | 0.933 | 0.933 | 0.933 |
| dev | `20260225_051505_dev_gemini_k1_v1` | 100 | 100 | 0 | 1.000 | 0.830 | 0.830 | 0.830 |
| test | `20260225_053241_test_gemini_k1_v1` | 200 | 199 | 1 | 1.000 | 0.899 | 0.899 | 0.899 |

Tracked artifacts:

- `results/baselines/pilot/20260224_233417/`
- `results/baselines/dev/20260225_051505_dev_gemini_k1_v1/`
- `results/baselines/test/20260225_053241_test_gemini_k1_v1/`

## Top Failure Modes (Test Split)

- `semantic_fail` (`19/200` attempts): wrong semantics despite valid `Prop`.
  - `ftt_test_0018`: `forall (a b : Bool), a && b = false`
    - `[semantic_fail] truth_table_mismatch:a := false, b := false`
  - `ftt_test_0019`: `forall (a b : Bool), a || b = false`
    - `[semantic_fail] truth_table_mismatch:a := true, b := false`
  - `ring_test_0016`: `forall (a b c d : R), (b + c + d) * a = b * a + c * a + d * a`
    - `[semantic_fail] ring_identity_mismatch ...`
- `shape_fail` (`1/200` attempts): candidate fails structural guard.
  - `ring_test_0064`: candidate uses 5 binders where expected has 4
    - `[shape_fail] binder_arity`
- `provider_error` (`1/200` attempts): transient provider/network failure.
  - `ftt_test_0040`
    - `provider_error:ConnectError:[Errno -3] Temporary failure in name resolution`

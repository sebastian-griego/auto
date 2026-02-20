# Autoformalization Eval Report

## Overall

- Total attempts: 30
- Test1 rate: 0.700
- Test2 rate: 0.667
- Combined rate: 0.667
- Pass@1: 0.667

## Model Table

| Model | Attempts | Items | Test1 | Test2 | Combined | Pass@k(max) |
|---|---:|---:|---:|---:|---:|---:|
| gemini:gemini-2.5-pro | 30 | 30 | 0.700 | 0.667 | 0.667 | 0.667 |

## Family Slice

- fin_truth_table: total=16 combined=0.625
- ring_identity: total=14 combined=0.714

## Tier Slice

- A: total=30 combined=0.667

## Buckets

- elab_fail: 6
- lean_parse_fail: 3
- pass: 20
- semantic_fail: 1

## Sample failures

- item `pilot_fintruth_001` bucket `elab_fail`
  - candidate: ``p = q``
  - stderr: ``
- item `pilot_fintruth_002` bucket `elab_fail`
  - candidate: `p && q = true`
  - stderr: ``
- item `pilot_fintruth_003` bucket `elab_fail`
  - candidate: ``p = true``
  - stderr: ``
- item `pilot_fintruth_006` bucket `elab_fail`
  - candidate: ``b = true ∧ x = 0``
  - stderr: ``
- item `pilot_fintruth_011` bucket `lean_parse_fail`
  - candidate: `(b : Bool) (x y : Fin 2), b = true ∧ x = y`
  - stderr: ``
- item `pilot_fintruth_015` bucket `elab_fail`
  - candidate: ``(b : Bool) × (x : Fin 3) → b = true ∧ x = 0``
  - stderr: ``
- item `pilot_ring_010` bucket `semantic_fail`
  - candidate: `(x z y : R) → x * y + z * y = (x + z) * y`
  - stderr: ``
- item `pilot_ring_011` bucket `lean_parse_fail`
  - candidate: `(x y z : R) : x * (y + z + 1) = x * y + x * z + x`
  - stderr: ``
- item `pilot_ring_013` bucket `elab_fail`
  - candidate: `(x + 2) * y = x * y + 2 * y`
  - stderr: ``
- item `pilot_ring_014` bucket `lean_parse_fail`
  - candidate: `(x y : R) : x * (y + 2) = x * y + x + x`
  - stderr: ``

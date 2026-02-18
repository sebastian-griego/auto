# Autoformalization Eval Report

## Overall

- Total attempts: 60
- Test1 rate: 0.333
- Test2 rate: 0.317
- Combined rate: 0.317
- Pass@1: 0.317

## Model Table

| Model | Attempts | Items | Test1 | Test2 | Combined | Pass@k(max) |
|---|---:|---:|---:|---:|---:|---:|
| gemini:gemini-2.5-pro | 30 | 30 | 0.667 | 0.633 | 0.633 | 0.633 |
| openai:gpt-5 | 30 | 30 | 0.000 | 0.000 | 0.000 | 0.000 |

## Family Slice

- fin_truth_table: total=32 combined=0.281
- ring_identity: total=28 combined=0.357

## Tier Slice

- A: total=60 combined=0.317

## Buckets

- elab_fail: 32
- lean_parse_fail: 8
- pass: 19
- semantic_fail: 1

## Sample failures

- item `pilot_fintruth_001` bucket `elab_fail`
  - candidate: ``
  - stderr: `runner_exception:OpenAI responses request failed (404): {
  "error": {
    "message": "Your organization must be verified to use the model `gpt-5`. Please go to: https://platform.o`
- item `pilot_fintruth_001` bucket `lean_parse_fail`
  - candidate: ``p = q``
  - stderr: ``
- item `pilot_fintruth_002` bucket `elab_fail`
  - candidate: ``
  - stderr: `runner_exception:OpenAI responses request failed (404): {
  "error": {
    "message": "Your organization must be verified to use the model `gpt-5`. Please go to: https://platform.o`
- item `pilot_fintruth_002` bucket `elab_fail`
  - candidate: `p && q = true`
  - stderr: ``
- item `pilot_fintruth_003` bucket `elab_fail`
  - candidate: ``
  - stderr: `runner_exception:OpenAI responses request failed (404): {
  "error": {
    "message": "Your organization must be verified to use the model `gpt-5`. Please go to: https://platform.o`
- item `pilot_fintruth_003` bucket `lean_parse_fail`
  - candidate: ``p = true``
  - stderr: ``
- item `pilot_fintruth_004` bucket `elab_fail`
  - candidate: ``
  - stderr: `runner_exception:OpenAI responses request failed (404): {
  "error": {
    "message": "Your organization must be verified to use the model `gpt-5`. Please go to: https://platform.o`
- item `pilot_fintruth_005` bucket `elab_fail`
  - candidate: ``
  - stderr: `runner_exception:OpenAI responses request failed (404): {
  "error": {
    "message": "Your organization must be verified to use the model `gpt-5`. Please go to: https://platform.o`
- item `pilot_fintruth_006` bucket `elab_fail`
  - candidate: ``
  - stderr: `runner_exception:OpenAI responses request failed (404): {
  "error": {
    "message": "Your organization must be verified to use the model `gpt-5`. Please go to: https://platform.o`
- item `pilot_fintruth_006` bucket `lean_parse_fail`
  - candidate: ``b = true ∧ x = 0``
  - stderr: ``

# Autoformalization Eval Report

## Overall

- Total attempts: 180
- Test1 rate: 0.322
- Test2 rate: 0.306
- Combined rate: 0.306
- Pass@3: 0.333

## Model Table

| Model | Attempts | Items | Test1 | Test2 | Combined | Pass@k(max) |
|---|---:|---:|---:|---:|---:|---:|
| gemini:gemini-2.5-pro | 90 | 30 | 0.644 | 0.611 | 0.611 | 0.667 |
| openai:gpt-5 | 90 | 30 | 0.000 | 0.000 | 0.000 | 0.000 |

## Family Slice

- fin_truth_table: total=96 combined=0.271
- ring_identity: total=84 combined=0.345

## Tier Slice

- A: total=180 combined=0.306

## Buckets

- elab_fail: 97
- lean_parse_fail: 25
- pass: 55
- semantic_fail: 3

## Sample failures

- item `pilot_fintruth_001` bucket `elab_fail`
  - candidate: ``
  - stderr: `runner_exception:OpenAI responses request failed (404): {
  "error": {
    "message": "Your organization must be verified to use the model `gpt-5`. Please go to: https://platform.o`
- item `pilot_fintruth_001` bucket `elab_fail`
  - candidate: ``
  - stderr: `runner_exception:OpenAI responses request failed (404): {
  "error": {
    "message": "Your organization must be verified to use the model `gpt-5`. Please go to: https://platform.o`
- item `pilot_fintruth_001` bucket `elab_fail`
  - candidate: ``
  - stderr: `runner_exception:OpenAI responses request failed (404): {
  "error": {
    "message": "Your organization must be verified to use the model `gpt-5`. Please go to: https://platform.o`
- item `pilot_fintruth_001` bucket `lean_parse_fail`
  - candidate: ``p = q``
  - stderr: ``
- item `pilot_fintruth_001` bucket `lean_parse_fail`
  - candidate: ``p = q``
  - stderr: ``
- item `pilot_fintruth_001` bucket `lean_parse_fail`
  - candidate: ``p = q``
  - stderr: ``
- item `pilot_fintruth_002` bucket `elab_fail`
  - candidate: ``
  - stderr: `runner_exception:OpenAI responses request failed (404): {
  "error": {
    "message": "Your organization must be verified to use the model `gpt-5`. Please go to: https://platform.o`
- item `pilot_fintruth_002` bucket `elab_fail`
  - candidate: ``
  - stderr: `runner_exception:OpenAI responses request failed (404): {
  "error": {
    "message": "Your organization must be verified to use the model `gpt-5`. Please go to: https://platform.o`
- item `pilot_fintruth_002` bucket `elab_fail`
  - candidate: ``
  - stderr: `runner_exception:OpenAI responses request failed (404): {
  "error": {
    "message": "Your organization must be verified to use the model `gpt-5`. Please go to: https://platform.o`
- item `pilot_fintruth_002` bucket `elab_fail`
  - candidate: `p && q = true`
  - stderr: ``

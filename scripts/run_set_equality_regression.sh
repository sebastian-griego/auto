#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_DIR="$ROOT/lean"

run_expect_pass() {
  local rel="$1"
  local abs="$LEAN_DIR/$rel"
  if ! (cd "$LEAN_DIR" && lake env lean "$abs") >/tmp/auto_set_regression.out 2>&1; then
    cat /tmp/auto_set_regression.out
    echo "expected pass but failed: $rel" >&2
    return 1
  fi
}

run_expect_semantic_fail() {
  local rel="$1"
  local abs="$LEAN_DIR/$rel"
  if (cd "$LEAN_DIR" && lake env lean "$abs") >/tmp/auto_set_regression.out 2>&1; then
    cat /tmp/auto_set_regression.out
    echo "expected failure but passed: $rel" >&2
    return 1
  fi
  if ! rg -q "\\[semantic_fail\\]" /tmp/auto_set_regression.out; then
    cat /tmp/auto_set_regression.out
    echo "expected semantic_fail tag in output: $rel" >&2
    return 1
  fi
}

run_expect_pass "AutoformalizationEval/Regression/SetEqualityV1PermutationPass.lean"
run_expect_semantic_fail "AutoformalizationEval/Regression/SetEqualityV1MismatchFail.lean"

echo "set_equality regression checks passed"

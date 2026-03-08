#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_DIR="$ROOT/lean"

run_expect_pass() {
  local rel="$1"
  local abs="$LEAN_DIR/$rel"
  if ! (cd "$LEAN_DIR" && lake env lean "$abs") >/tmp/auto_linear_regression.out 2>&1; then
    cat /tmp/auto_linear_regression.out
    echo "expected pass but failed: $rel" >&2
    return 1
  fi
}

run_expect_semantic_fail() {
  local rel="$1"
  local abs="$LEAN_DIR/$rel"
  if (cd "$LEAN_DIR" && lake env lean "$abs") >/tmp/auto_linear_regression.out 2>&1; then
    cat /tmp/auto_linear_regression.out
    echo "expected failure but passed: $rel" >&2
    return 1
  fi
  if ! rg -q "\\[semantic_fail\\]" /tmp/auto_linear_regression.out; then
    cat /tmp/auto_linear_regression.out
    echo "expected semantic_fail tag in output: $rel" >&2
    return 1
  fi
}

run_expect_shape_fail() {
  local rel="$1"
  local abs="$LEAN_DIR/$rel"
  if (cd "$LEAN_DIR" && lake env lean "$abs") >/tmp/auto_linear_regression.out 2>&1; then
    cat /tmp/auto_linear_regression.out
    echo "expected failure but passed: $rel" >&2
    return 1
  fi
  if ! rg -q "\\[shape_fail\\]" /tmp/auto_linear_regression.out; then
    cat /tmp/auto_linear_regression.out
    echo "expected shape_fail tag in output: $rel" >&2
    return 1
  fi
}

run_expect_pass "AutoformalizationEval/Regression/LinearInequalityEquivalentPass.lean"
run_expect_semantic_fail "AutoformalizationEval/Regression/LinearInequalityRelationMismatchFail.lean"
if ! rg -q "linear_inequality_relation_mismatch" /tmp/auto_linear_regression.out; then
  cat /tmp/auto_linear_regression.out
  echo "expected relation mismatch detail in semantic failure output" >&2
  exit 1
fi
run_expect_semantic_fail "AutoformalizationEval/Regression/LinearInequalityCoefficientMismatchFail.lean"
if ! rg -q "coeffs=\\[" /tmp/auto_linear_regression.out; then
  cat /tmp/auto_linear_regression.out
  echo "expected normalized coefficient detail in mismatch output" >&2
  exit 1
fi
run_expect_semantic_fail "AutoformalizationEval/Regression/LinearInequalityOutOfFragmentFail.lean"
if ! rg -q "nonlinear_mul" /tmp/auto_linear_regression.out; then
  cat /tmp/auto_linear_regression.out
  echo "expected nonlinear_mul detail in out-of-fragment output" >&2
  exit 1
fi
run_expect_shape_fail "AutoformalizationEval/Regression/LinearInequalityShapeReject.lean"

echo "linear_inequality regression checks passed"

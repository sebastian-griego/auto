#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if command -v lake >/dev/null 2>&1; then
  (
    cd "$ROOT/lean"
    lake exe cache get || true
    lake build
  )
else
  echo "lake not found; skipping Lean build"
fi

python -m pip install -e "$ROOT/harness"

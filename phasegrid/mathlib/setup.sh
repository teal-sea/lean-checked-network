#!/usr/bin/env bash
set -u
export PATH=$HOME/.elan/bin:$PATH
cd "$(dirname "$0")"
echo "=== start $(date -u +%FT%TZ)"
elan toolchain install leanprover/lean4:v4.35.0 2>&1 | tail -3
echo "=== toolchain installed $(date -u +%FT%TZ)"
lake --version
echo "=== lake update"
lake update 2>&1 | tail -5
echo "=== lake update done $(date -u +%FT%TZ)"
echo "=== cache get"
lake exe cache get 2>&1 | tail -5
echo "=== cache get done $(date -u +%FT%TZ)"
echo 'import Mathlib
#eval Lean.versionString' > vcheck.lean
lake env lean vcheck.lean 2>&1 | tail -3; rm -f vcheck.lean
echo "=== import Mathlib test done $(date -u +%FT%TZ)"
cat lake-manifest.json | grep -A3 '"mathlib"' | head -8

#!/usr/bin/env bash
# Mechanical copy of the retained core sources (../lean/Transformer/{Model,Fast,Equiv}.lean) into this Lake project as
# TransformerCore.*, with the word `Transformer` renamed to `TransformerCore` (the names `expFix`, `logits`, `horner`, ...
# collide with the Mathlib-side `Transformer` namespace). No other edit. Usage: sync_core.sh [--check]
set -eu
cd "$(dirname "$0")"
mkdir -p TransformerCore
rc=0
for m in Model Fast Equiv; do
  src=../lean/Transformer/$m.lean
  dst=TransformerCore/$m.lean
  gen=$(perl -pe 's/\bTransformer\b/TransformerCore/g' "$src")
  if [ "${1:-}" = "--check" ]; then
    if [ "$gen" = "$(cat "$dst")" ]; then echo "ok   $dst is the renamed $src"; else echo "DIFF $dst differs from the renamed $src"; rc=1; fi
  else
    printf '%s\n' "$gen" > "$dst"
  fi
done
exit $rc

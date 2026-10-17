#!/usr/bin/env bash
# Free public CI only. Positive status requires real compilation, exact selected
# axiom audit, every mirrored module replay, and an expected-failure control.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
case "$LEAN_NUM_THREADS" in 1|2) ;; *) echo 'bounds status=FAIL: only 1 or 2 Lean threads allowed'; exit 1;; esac
cd "$(dirname "$0")"
out=bounds-out
mkdir -p "$out"
trap 'rc=$?; if [ "$rc" -ne 0 ]; then echo "bounds status=FAIL exit=$rc"; fi' EXIT
step() {
  local name=$1 secs=$2; shift 2
  echo "=== $name start $(date -u +%FT%TZ)"
  if timeout -s TERM -k 20 "$secs" "$@" > "$out/$name.out" 2>&1; then
    echo "$name status=OK"
  else
    local rc=$?; cat "$out/$name.out"; echo "$name status=FAIL exit=$rc"; return "$rc"
  fi
}
sha256sum TransformerBridge/Bounds.lean TransformerBridge/FrozenBounds.lean bounds_axioms.lean sync_core.sh sync_core.py \
  bounds.sh check_bounds_audit.py test_bounds_harness.py ../../.github/workflows/transformer.yml \
  > "$out/candidate.sha256"
cat "$out/candidate.sha256"
# All 16 retained inputs must still agree with the existing frozen-input digest file.
(cd ../lean && sha256sum -c cached-inputs.sha256) > "$out/frozen-inputs.out" 2>&1
# Fail on generic integration errors before emitting any frozen numeric mirror.
step support_sync 60 ./sync_core.sh --support-only --manifest "$out/support.tsv"
step support_check 60 ./sync_core.sh --support-only --check
support_modules=(); support_sources=()
while IFS=$'\t' read -r module _source target _source_hash _target_hash; do
  support_modules+=("$module"); support_sources+=("$target")
done < "$out/support.tsv"
[ "${#support_modules[@]}" -eq 4 ]
step support_scan 60 ../lean/scan_sources.sh "${support_sources[@]}" TransformerBridge/Bounds.lean
for module in "${support_modules[@]}"; do
  step "support_build_$module" 900 lake build "$module"
done
step support_build_bridge 900 lake build TransformerBridge.Bridge
step support_build_bounds 900 lake build TransformerBridge.Bounds
step sync 60 ./sync_core.sh --bounds --manifest "$out/sync.tsv"
step sync_check 60 ./sync_core.sh --bounds --check
# The manifest records both byte hashes and topological build/replay order.
cat "$out/sync.tsv"
modules=(); sources=()
while IFS=$'\t' read -r module _source target _source_hash _target_hash; do
  modules+=("$module"); sources+=("$target")
done < "$out/sync.tsv"
[ "${#modules[@]}" -eq 30 ] && [ "${#sources[@]}" -eq 30 ]
step scan 60 ../lean/scan_sources.sh "${sources[@]}" TransformerBridge/Bounds.lean TransformerBridge/FrozenBounds.lean
# Serial invocations in this .lake; no rc2 compiled artifacts are used.
# Finish every numeric dependency before bridge.sh requests the aggregate library.
for module in "${modules[@]}"; do
  step "build_$module" 900 lake build "$module"
done
step bridge 1200 ./bridge.sh
step build_TransformerBridge.Bounds 900 lake build TransformerBridge.Bounds
step build_TransformerBridge.FrozenBounds 900 lake build TransformerBridge.FrozenBounds
step axioms 300 lake env lean bounds_axioms.lean
step selected_audit 60 python3 check_bounds_audit.py "$out/axioms.out"
cat "$out/selected_audit.out"
# A true bounds theorem must never make a strictly smaller scalar bound true.
cat > "$out/negative.lean" <<'LEAN'
import TransformerBridge.FrozenBounds
example : Transformer.chosenBounds.G < 17767350 := by decide +kernel
LEAN
set +e
timeout -s TERM -k 20 120 lake env lean "$out/negative.lean" > "$out/negative.out" 2>&1
negative_rc=$?
set -e
[ "$negative_rc" -eq 1 ]
grep -q "decide" "$out/negative.out"
grep -q "false" "$out/negative.out"
echo 'negative-control status=EXPECTED_FAILURE'
replayed=0
for module in "${modules[@]}" TransformerBridge.Bridge TransformerBridge.Bounds TransformerBridge.FrozenBounds; do
  step "replay_$module" 900 lake env leanchecker "$module"
  replayed=$((replayed + 1))
done
[ "$replayed" -eq 33 ]
echo "bounds status=KERNEL_ACCEPTED selected-declarations=10/10 replayed=$replayed/33"

#!/usr/bin/env bash
# Build and check the bridge: TransformerCore (renamed copy of the core Model/Fast/Equiv) and TransformerBridge.Bridge.
# One module per lake call, per-step timeout, every exit code gating, outputs kept in bridge-out/.
set -u
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
cd "$(dirname "$0")" || exit 1
out=bridge-out; mkdir -p "$out"; status=0
step() { # name, timeout seconds, command...
  local name=$1 secs=$2; shift 2
  echo "=== $name start $(date -u +%T)"
  timeout -s TERM -k 20 "$secs" "$@" > "$out/$name.out" 2>&1; local rc=$?
  echo "$name exit $rc: $(grep -E 'Build completed|error' "$out/$name.out" | head -3 | tr '\n' ' ')"
  [ "$rc" -eq 0 ] || { status=1; cat "$out/$name.out"; }
  return "$rc"
}
./sync_core.sh --check || status=1
step build_core 1200 lake build TransformerCore || { echo "TransformerCore failed"; exit 1; }
step build_bridge 2400 lake build TransformerBridge.Bridge || { echo "Bridge failed"; exit 1; }
echo "=== source scan (must be empty)"
grep -nE "sorry|native_decide|^\s*axiom |opaque |implemented_by|extern|skipKernelTC|decide \+native" \
  TransformerCore/*.lean TransformerBridge/*.lean TransformerBridge.lean TransformerCore.lean && status=1 || echo "none found"
cat > "$out/axioms.lean" <<'LEAN'
import TransformerBridge.Bridge
#print axioms TransformerCore.fastCheck_correct
#print axioms TransformerBridge.expFix_eq
#print axioms TransformerBridge.logits_nth_eq
#print axioms TransformerBridge.hA_of_fastCheck
LEAN
step axioms 600 lake env lean "$out/axioms.lean"; cat "$out/axioms.out"
n=$(grep -cE "^.[^ ]+. (does not depend on any axioms|depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\])$" "$out/axioms.out")
echo "$n of 4 theorems on standard axioms or none"; [ "$n" -eq 4 ] || status=1
step replay_bridge 1800 lake env leanchecker TransformerBridge.Bridge
echo "=== done $(date -u +%T), exit $status"; exit $status

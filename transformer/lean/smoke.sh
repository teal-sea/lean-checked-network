#!/usr/bin/env bash
# Core-Lean smoke: build Transformer (Model, Fast, Equiv), then Transformer.Net.Rows00, which pulls in
# Weights, Table (tables_ok) and the first row only. Never builds Net.AllInputs or the other 112 rows.
# Writes time and peak memory per step and every Lean output to ci-out/ so a failure leaves evidence.
set -u
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
cd "$(dirname "$0")" || exit 1
out=ci-out; mkdir -p "$out"
status=0
echo "=== versions"; cat lean-toolchain; lean --version; nproc; free -m | head -2
step() { # name, command...
  local name=$1; shift
  echo "=== $name start $(date -u +%FT%TZ)"
  /usr/bin/time -v -o "$out/$name.time" "$@" > "$out/$name.out" 2>&1; local rc=$?
  echo "$name exit $rc; wall $(grep 'Elapsed' "$out/$name.time" | sed 's/.*): //'); max RSS KB $(grep 'Maximum resident' "$out/$name.time" | sed 's/.*: //')"
  grep -E "error|Build completed" "$out/$name.out" | head -5
  [ $rc -eq 0 ] || status=1
  return $rc
}
step build_core lake build Transformer || { echo "core build failed, stopping"; echo "exit $status"; exit 1; }
step build_row0 lake build Transformer.Net.Rows00 || { echo "row0 failed"; exit 1; }
echo "=== source scan (must be empty): sorry, native_decide, axiom, opaque, implemented_by, extern, skipKernelTC"
./scan_sources.sh Transformer/Model.lean Transformer/Fast.lean Transformer/Equiv.lean Transformer/Net/Table.lean Transformer/Net/Rows00.lean Transformer.lean > "$out/scan.out" 2>&1; sc=$?
cat "$out/scan.out"
case $sc in 0) echo "none found" ;; 1) echo "forbidden construct found"; status=1 ;; *) echo "scan error $sc"; status=1 ;; esac
cat > "$out/axioms.lean" <<'LEAN'
import Transformer.Net.Rows00
#print axioms Transformer.fastCheck_correct
#print axioms Transformer.Net.tables_ok
#print axioms Transformer.Net.fast_0
LEAN
step axioms lake env lean "$out/axioms.lean"; cat "$out/axioms.out"
n=$(grep -cE "^.[^ ]+. (does not depend on any axioms|depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\])$" "$out/axioms.out")
echo "$n of 3 theorems on standard axioms or none"; [ "$n" -eq 3 ] || status=1
echo "=== leanchecker replay of Equiv and Rows00, both gating"
step replay_equiv lake env leanchecker Transformer.Equiv
step replay_row0 lake env leanchecker Transformer.Net.Rows00 || echo "row0 replay failed (gating: exit stays nonzero)"
echo "=== done $(date -u +%FT%TZ), exit $status"; exit $status

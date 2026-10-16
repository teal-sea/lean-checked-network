#!/usr/bin/env bash
# Kernel-check the three fixed-phase networks, print their axioms, replay every module with leanchecker.
set -u
export PATH="/root/.elan/bin:$PATH"
cd "$(dirname "$0")/lean"
status=0
for name in FixedPhase12 FixedPhase16 FixedPhase40 FixedPhase448; do
  echo "=== build $name start $(date -u +%FT%TZ)"
  t0=$(date +%s); lake build LeanCheckedNetwork.$name.AllInputs > /tmp/build_$name.out 2>&1; b=$?; echo "wall $(( $(date +%s) - t0 ))s" >> /tmp/build_$name.out
  grep -E "✖|error|Build completed|warning|wall " /tmp/build_$name.out | tail -5
  echo "=== build $name exit $b end $(date -u +%FT%TZ)"
  [ $b -eq 0 ] || status=1
done
echo "=== axioms"
cat > /tmp/axioms_check.lean <<'LEAN'
import LeanCheckedNetwork.FixedPhase12.AllInputs
import LeanCheckedNetwork.FixedPhase16.AllInputs
import LeanCheckedNetwork.FixedPhase40.AllInputs
import LeanCheckedNetwork.FixedPhase448.AllInputs
#print axioms LeanCheckedNetwork.FixedPhase12.adds_mod_113
#print axioms LeanCheckedNetwork.FixedPhase16.adds_mod_113
#print axioms LeanCheckedNetwork.FixedPhase40.adds_mod_113
#print axioms LeanCheckedNetwork.FixedPhase448.adds_mod_113
LEAN
lake env lean /tmp/axioms_check.lean 2>&1 | tee /tmp/axioms.out
nstd=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" /tmp/axioms.out)
[ "$nstd" -eq 4 ] && echo "all four theorems use only the standard axioms" || { echo "PROBLEM: unexpected axioms"; status=1; }
echo "=== replay with leanchecker, 4 at a time"
mods=$(find LeanCheckedNetwork/FixedPhase12 LeanCheckedNetwork/FixedPhase16 LeanCheckedNetwork/FixedPhase40 LeanCheckedNetwork/FixedPhase448 -name '*.lean' | sed 's/\.lean$//; s|/|.|g' | sort)
mods="LeanCheckedNetwork.Network LeanCheckedNetwork.Fast $mods"
nmods=$(printf '%s\n' $mods | wc -l)
printf '%s\n' $mods | xargs -P 4 -I{} sh -c 'if lake env leanchecker {} > /tmp/lc.{}.out 2>&1; then echo "OK   {}"; else echo "FAIL {}"; cat /tmp/lc.{}.out; fi' > /tmp/replay.out
sort /tmp/replay.out | grep -c '^OK' | xargs -I{} echo "replayed {} of $nmods modules"
grep '^FAIL' /tmp/replay.out && status=1
echo "=== done $(date -u +%FT%TZ) status $status"
exit $status

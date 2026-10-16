#!/usr/bin/env bash
# Kernel-check the fixed-phase networks (four at modulus 113, then moduli 7, 12 and 257), print their
# axioms, check the planted fault is rejected, replay every module with leanchecker.
set -u
export PATH="/root/.elan/bin:$PATH"
cd "$(dirname "$0")/lean"
status=0
STAGE=${STAGE:-all}
if [ "$STAGE" != replay ]; then
for name in FixedPhase12 FixedPhase16 FixedPhase40 FixedPhase448 Mod7All Mod12All Mod257Min; do
  echo "=== build $name start $(date -u +%FT%TZ)"
  t0=$(date +%s); b=0
  if [ "$name" = FixedPhase448 ]; then
    # Lake has no jobs flag and a 448-wide row file needs up to 5 GB, so build its row files one at a time.
    : > /tmp/build_$name.out
    for i in $(seq -f "%02g" 0 15); do lake build LeanCheckedNetwork.$name.Rows$i >> /tmp/build_$name.out 2>&1 || b=1; done
    lake build LeanCheckedNetwork.$name.AllInputs >> /tmp/build_$name.out 2>&1 || b=1
  else
    lake build LeanCheckedNetwork.$name.AllInputs > /tmp/build_$name.out 2>&1 || b=1
  fi
  echo "wall $(( $(date +%s) - t0 ))s" >> /tmp/build_$name.out
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
import LeanCheckedNetwork.Mod7All.AllInputs
import LeanCheckedNetwork.Mod12All.AllInputs
import LeanCheckedNetwork.Mod257Min.AllInputs
import LeanCheckedNetwork.Fault.Fixed12Count
#print axioms LeanCheckedNetwork.FixedPhase12.adds_mod_113
#print axioms LeanCheckedNetwork.FixedPhase16.adds_mod_113
#print axioms LeanCheckedNetwork.FixedPhase40.adds_mod_113
#print axioms LeanCheckedNetwork.FixedPhase448.adds_mod_113
#print axioms LeanCheckedNetwork.Mod7All.adds_mod_7
#print axioms LeanCheckedNetwork.Mod12All.adds_mod_12
#print axioms LeanCheckedNetwork.Mod257Min.adds_mod_257
#print axioms LeanCheckedNetwork.FaultFixed12.right_on_12753
LEAN
lake env lean /tmp/axioms_check.lean 2>&1 | tee /tmp/axioms.out
nstd=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" /tmp/axioms.out)
[ "$nstd" -eq 8 ] && echo "all eight theorems use only the standard axioms" || { echo "PROBLEM: unexpected axioms"; status=1; }
echo "=== planted fault (must be rejected by the kernel)"
if ! lake build LeanCheckedNetwork.Fault.Fixed12Table LeanCheckedNetwork.Fault.Fixed12Count > /tmp/fault12_table.out 2>&1; then
  echo "PROBLEM: the faulty network's table did not build, so the check did not run"; tail -5 /tmp/fault12_table.out; status=1
elif lake env lean expected_fail/FaultFixed12Row.lean > /tmp/fault12.out 2>&1; then
  echo "PROBLEM: the faulty network was accepted"; status=1
elif grep -q "(kernel)" /tmp/fault12.out; then
  echo "rejected by the kernel, as it should be:"; grep -m1 "(kernel)" /tmp/fault12.out
else
  echo "PROBLEM: failed for a reason other than the kernel rejecting it:"; head -5 /tmp/fault12.out; status=1
fi
fi
if [ "$STAGE" != build ]; then
echo "=== replay with leanchecker, 2 at a time"
mods=$(find LeanCheckedNetwork/FixedPhase12 LeanCheckedNetwork/FixedPhase16 LeanCheckedNetwork/FixedPhase40 LeanCheckedNetwork/FixedPhase448 LeanCheckedNetwork/Mod7All LeanCheckedNetwork/Mod12All LeanCheckedNetwork/Mod257Min -name '*.lean' | sed 's/\.lean$//; s|/|.|g' | sort)
mods="LeanCheckedNetwork.Network LeanCheckedNetwork.Fast LeanCheckedNetwork.Count LeanCheckedNetwork.Fault.Fixed12Weights LeanCheckedNetwork.Fault.Fixed12Table LeanCheckedNetwork.Fault.Fixed12Count $mods"
nmods=$(printf '%s\n' $mods | wc -l)
printf '%s\n' $mods | xargs -P 2 -I{} sh -c 'if lake env leanchecker {} > /tmp/lc.{}.out 2>&1; then echo "OK   {}"; else echo "FAIL {}"; cat /tmp/lc.{}.out; fi' > /tmp/replay.out
sort /tmp/replay.out | grep -c '^OK' | xargs -I{} echo "replayed {} of $nmods modules"
grep '^FAIL' /tmp/replay.out && status=1
fi
echo "=== done $(date -u +%FT%TZ) status $status"
exit $status

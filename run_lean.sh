#!/usr/bin/env bash
# Check both networks with Lean's kernel, replay every module with leanchecker (it rechecks the
# compiled files with the kernel, so options like debug.skipKernelTC cannot hide anything), run
# the planted-fault check, print the axioms. Exits non-zero if any step fails.
# JOBS sets how many modules are replayed at once (default 4, about 2 GB each).
set -u
cd "$(dirname "$0")/lean"
export PATH="$HOME/.elan/bin:$PATH"
status=0
echo "=== build start $(date -u +%FT%TZ)"
lake build LeanCheckedNetwork > /tmp/build.out 2>&1; b=$?
grep -E "✖|error|Build completed|warning" /tmp/build.out
echo "=== build exit $b end $(date -u +%FT%TZ)"
[ $b -eq 0 ] || status=1
JOBS=${JOBS:-4}
echo "=== replay every module with leanchecker, $JOBS at a time"
# Every module with declarations. The root file LeanCheckedNetwork.lean only imports these; replaying
# it rechecks all of them at once (over 9 GB), so it is left out: each declaration is replayed once here.
# FixedPhase448 and Mod257Min are not in the root build (an hour and up to 5 GB each); run_lean_fixed_phase.sh
# checks and replays them, and lean_run_fixed_phase.log is its record.
mods=$(find LeanCheckedNetwork -name '*.lean' -not -path '*/Fault/*' -not -path '*/FixedPhase448/*' -not -path '*/Mod257Min/*' | sed 's/\.lean$//; s|/|.|g' | sort)
nmods=$(printf '%s\n' $mods | wc -l)
printf '%s\n' $mods | xargs -P "$JOBS" -I{} sh -c \
  'if lake env leanchecker {} > /tmp/leanchecker.{}.out 2>&1; then echo "OK   {}"; else echo "FAIL {}"; cat /tmp/leanchecker.{}.out; fi' \
  > /tmp/replay.out
sort /tmp/replay.out
nok=$(grep -c '^OK' /tmp/replay.out)
echo "replayed $nok of $nmods modules"
[ "$nok" -eq "$nmods" ] || status=1
echo "=== planted fault (must be rejected by the kernel)"
if ! lake build LeanCheckedNetwork.Fault.Table > /tmp/fault_table.out 2>&1; then
  echo "PROBLEM: the faulty network's table did not build, so the check did not run"; tail -5 /tmp/fault_table.out; status=1
elif lake env lean expected_fail/FaultRow.lean > /tmp/fault.out 2>&1; then
  echo "PROBLEM: the faulty network was accepted"; status=1
elif grep -q "(kernel)" /tmp/fault.out; then
  echo "rejected by the kernel, as it should be:"; grep -m1 "(kernel)" /tmp/fault.out
else
  echo "PROBLEM: failed for a reason other than the kernel rejecting it:"; head -5 /tmp/fault.out; status=1
fi
echo "=== axioms"
cat > /tmp/axioms_check.lean <<'LEAN'
import LeanCheckedNetwork
#print axioms LeanCheckedNetwork.Trained.adds_mod_113
#print axioms LeanCheckedNetwork.CircleOnly.adds_mod_113
#print axioms LeanCheckedNetwork.FixedPhase12.adds_mod_113
#print axioms LeanCheckedNetwork.FixedPhase16.adds_mod_113
#print axioms LeanCheckedNetwork.FixedPhase40.adds_mod_113
#print axioms LeanCheckedNetwork.Mod7All.adds_mod_7
#print axioms LeanCheckedNetwork.Mod12All.adds_mod_12
#print axioms LeanCheckedNetwork.H64Step2000.right_on_12766
#print axioms LeanCheckedNetwork.H64Step4000.right_on_12767
#print axioms LeanCheckedNetwork.H64Step6000.right_on_12766
#print axioms LeanCheckedNetwork.H64Step8000.right_on_12767
#print axioms LeanCheckedNetwork.H64Step10000.right_on_12767
#print axioms LeanCheckedNetwork.H64Step12000.right_on_12769
LEAN
lake env lean /tmp/axioms_check.lean > /tmp/axioms.out 2>&1; cat /tmp/axioms.out
nstd=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" /tmp/axioms.out)
if [ "$nstd" -eq 13 ]; then echo "all thirteen theorems use only the standard axioms"; else echo "PROBLEM: unexpected axioms"; status=1; fi
echo "=== done $(date -u +%FT%TZ)"
exit $status

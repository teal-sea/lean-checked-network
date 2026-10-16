#!/usr/bin/env bash
# The last-pair faults: regenerate the two faulty networks from the committed tables, build their tables
# (one Lake call per module: a 448-neuron Weights module peaks near 4.4 GB), confirm the kernel rejects
# both expected_fail files, then print the kernel's own six verdicts through addDecl. About 6 minutes.
set -u
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")"
status=0
echo "=== last-pair faults (must be rejected by the kernel) $(date -u +%FT%TZ)"
python3 gen_last_fault.py || { echo "PROBLEM: gen_last_fault.py failed"; exit 1; }
for m in P7LastFault.Table P7Full.Table P113LastFault.Table P113Full.Table; do
  t0=$(date +%s)
  if ! lake build PhaseGridInstances.$m > last_fault_build.$m.out 2>&1; then
    echo "PROBLEM: PhaseGridInstances.$m did not build, so the check did not run"; tail -5 last_fault_build.$m.out; exit 1
  fi
  echo "built PhaseGridInstances.$m, $(( $(date +%s) - t0 )) s"
done
expect_fail() {  # $1 file that must fail, $2 output file
  if lake env lean "$1" > "$2" 2>&1; then
    echo "PROBLEM: $1 was accepted"; status=1
  elif grep -qE "\(kernel\)|proved that the proposition" "$2" && ! grep -q "(kernel) declaration has metavariables" "$2"; then
    echo "$1 rejected by the kernel, as it should be:"; grep -m1 -E "\(kernel\)|proved that the proposition|is false" "$2"
  else
    echo "PROBLEM: $1 failed for a reason other than the kernel rejecting it:"; head -5 "$2"; status=1
  fi
}
expect_fail expected_fail/P7LastRow.lean last_fault_p7.out
expect_fail expected_fail/P113LastChunk.lean last_fault_p113.out
t0=$(date +%s)
lake env lean kernel_reject_last.lean > last_fault_kernel.out 2>&1
echo "=== kernel verdicts through addDecl, $(( $(date +%s) - t0 )) s"
grep -oE "kernel (ACCEPTED|REJECTED) [A-Za-z0-9_]+(: \(kernel\) [a-z ]+)?" last_fault_kernel.out
for want in "ACCEPTED fault7_row6_first6" "REJECTED fault7_row6_all" "ACCEPTED real7_row6" \
            "ACCEPTED fault113_row112_b90_111" "REJECTED fault113_row112_b90_112" "ACCEPTED real113_row112_b90_112"; do
  grep -q "kernel $want" last_fault_kernel.out || { echo "PROBLEM: expected 'kernel $want'"; status=1; }
done
echo "=== done $(date -u +%FT%TZ), exit $status"
exit $status

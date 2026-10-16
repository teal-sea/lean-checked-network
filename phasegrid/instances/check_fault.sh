#!/usr/bin/env bash
# The planted fault: build the faulty network's table, then confirm the kernel rejects expected_fail/FaultRow.lean.
set -u
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")"
status=0
echo "=== planted fault (must be rejected by the kernel) $(date -u +%FT%TZ)"
if ! lake build PhaseGridInstances.P7Fault.Table > fault_table.out 2>&1; then
  echo "PROBLEM: the faulty network's table did not build, so the check did not run"; tail -5 fault_table.out; status=1
elif lake env lean expected_fail/FaultRow.lean > fault.out 2>&1; then
  echo "PROBLEM: the faulty network was accepted"; status=1
elif grep -qE "\(kernel\)|proved that the proposition" fault.out && ! grep -q "(kernel) declaration has metavariables" fault.out; then
  echo "rejected by the kernel, as it should be:"; grep -m1 -E "\(kernel\)|proved that the proposition|is false" fault.out
else
  echo "PROBLEM: failed for a reason other than the kernel rejecting it:"; head -5 fault.out; status=1
fi
echo "=== done $(date -u +%FT%TZ), exit $status"
exit $status

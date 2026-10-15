#!/usr/bin/env bash
# Check both networks with Lean's kernel, run the planted-fault check, print the axioms.
set -u
cd "$(dirname "$0")/lean"
export PATH="$HOME/.elan/bin:$PATH"
echo "=== build start $(date -u +%FT%TZ)"
lake build LeanCheckedNetwork 2>&1 | grep -E "✔|✖|error|Build" | grep -v "Weights\|Network\b"
echo "=== build exit ${PIPESTATUS[0]} end $(date -u +%FT%TZ)"
echo "=== planted fault (must be rejected by the kernel)"
if ! lake build LeanCheckedNetwork.Fault.Table > /tmp/fault_table.out 2>&1; then
  echo "PROBLEM: the faulty network's table did not build, so the check did not run"; tail -5 /tmp/fault_table.out
elif lake env lean expected_fail/FaultRow.lean > /tmp/fault.out 2>&1; then
  echo "PROBLEM: the faulty network was accepted"
elif grep -q "(kernel)" /tmp/fault.out; then
  echo "rejected by the kernel, as it should be:"; grep -m1 "(kernel)" /tmp/fault.out
else
  echo "PROBLEM: failed for a reason other than the kernel rejecting it:"; head -5 /tmp/fault.out
fi
echo "=== axioms"
cat > /tmp/axioms_check.lean <<'LEAN'
import LeanCheckedNetwork
#print axioms LeanCheckedNetwork.Trained.adds_mod_113
#print axioms LeanCheckedNetwork.CircleOnly.adds_mod_113
LEAN
lake env lean /tmp/axioms_check.lean
echo "=== done $(date -u +%FT%TZ)"

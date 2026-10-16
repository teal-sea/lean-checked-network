#!/usr/bin/env bash
# Build the Lean package, replay every module with leanchecker, run the planted faults (they must
# be rejected), print the axioms of the main theorems. Exits non-zero if any step fails.
set -u
cd "$(dirname "$0")/lean"
export PATH="$HOME/.elan/bin:$PATH"
status=0
echo "=== build start $(date -u +%FT%TZ)"
s=$(date +%s.%N)
lake build RnnAdder > /tmp/rnn_build.out 2>&1; b=$?
grep -E "✖|error|Build completed" /tmp/rnn_build.out
echo "=== build exit $b, $(echo "$(date +%s.%N) - $s" | bc) s"
[ $b -eq 0 ] || status=1
echo "=== replay every module with leanchecker"
for m in $(find RnnAdder -name '*.lean' | sed 's/\.lean$//; s|/|.|g' | sort); do
  s=$(date +%s.%N)
  if lake env leanchecker "$m" > /tmp/rnn_lc.out 2>&1; then echo "OK   $m ($(echo "$(date +%s.%N) - $s" | bc) s)"
  else echo "FAIL $m"; cat /tmp/rnn_lc.out; status=1; fi
done
echo "=== planted faults (each must be rejected)"
for f in expected_fail/*.lean; do
  if lake env lean "$f" > /tmp/rnn_fault.out 2>&1; then echo "PROBLEM: $f was accepted"; status=1
  elif grep -q "proved that the proposition" /tmp/rnn_fault.out && grep -q "is false" /tmp/rnn_fault.out; then
    echo "rejected, as it should be: $f"; grep -m1 -A2 "error" /tmp/rnn_fault.out | sed 's/^/    /'
  else echo "PROBLEM: $f failed for another reason:"; head -5 /tmp/rnn_fault.out; status=1; fi
done
echo "=== axioms"
cat > /tmp/rnn_axioms.lean <<'LEAN'
import RnnAdder
#print axioms RnnAdder.Trained.adds
#print axioms RnnAdder.Trained.sums_correct
#print axioms RnnAdder.Trained.carry_correct
LEAN
lake env lean /tmp/rnn_axioms.lean > /tmp/rnn_axioms.out 2>&1; cat /tmp/rnn_axioms.out
nbad=$(grep -vc "depends on axioms: \[propext, Quot.sound\]$" /tmp/rnn_axioms.out)
if [ "$nbad" -eq 0 ]; then echo "all three theorems use only propext and Quot.sound (a subset of the standard axioms)"; else echo "PROBLEM: unexpected axioms"; status=1; fi
echo "=== no sorry / native_decide / axiom / opaque / implemented_by / extern in the sources"
if grep -nE "sorry|native_decide|^axiom|^opaque|implemented_by|extern|skipKernelTC" RnnAdder/*.lean RnnAdder.lean; then echo "PROBLEM: forbidden token found"; status=1; else echo "none found"; fi
echo "=== done $(date -u +%FT%TZ), status $status"
exit $status

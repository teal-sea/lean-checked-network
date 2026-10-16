#!/usr/bin/env bash
# Usage: check_instance.sh NAME P JOBS   (build one instance with the kernel, replay with leanchecker, print axioms)
set -u
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")"
NAME=$1; P=$2; JOBS=${3:-3}
status=0
echo "=== $NAME build start $(date -u +%FT%TZ)  (lean $(cat lean-toolchain); lake uses all cores, replay $JOBS at a time)"
t0=$(date +%s)
lake build PhaseGridInstances.$NAME.AllInputs > build.$NAME.out 2>&1; b=$?
grep -E "✖|error|Build completed|warning|sorry" build.$NAME.out | head -20
t1=$(date +%s)
echo "=== $NAME build exit $b, wall $((t1-t0)) s, end $(date -u +%FT%TZ)"
[ $b -eq 0 ] || status=1
mods=$(find PhaseGridInstances/$NAME -name '*.lean' | sed 's/\.lean$//; s|/|.|g' | sort)
mods="PhaseGridInstances.Network PhaseGridInstances.Fast $mods"
nmods=$(printf '%s\n' $mods | wc -l)
echo "=== replay $nmods modules with leanchecker, $JOBS at a time"
printf '%s\n' $mods | xargs -P "$JOBS" -I{} sh -c \
  'if lake env leanchecker {} > leanchecker.{}.out 2>&1; then echo "OK   {}"; else echo "FAIL {}"; cat leanchecker.{}.out; fi' \
  > replay.$NAME.out
sort replay.$NAME.out
nok=$(grep -c '^OK' replay.$NAME.out)
t2=$(date +%s)
echo "replayed $nok of $nmods modules, wall $((t2-t1)) s"
[ "$nok" -eq "$nmods" ] || status=1
echo "=== axioms"
printf 'import PhaseGridInstances.%s.AllInputs\n#print axioms PhaseGridInstances.%s.adds_mod_%s\n' $NAME $NAME $P > axioms.$NAME.lean
lake env lean axioms.$NAME.lean 2>&1 | tee axioms.$NAME.out
grep -q "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" axioms.$NAME.out || { echo "PROBLEM: unexpected axioms"; status=1; }
echo "=== $NAME done $(date -u +%FT%TZ), exit $status"
exit $status

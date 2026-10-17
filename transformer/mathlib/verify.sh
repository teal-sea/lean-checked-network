#!/usr/bin/env bash
# Verification of transformer/mathlib: build one module per lake call under the shared lock, replay
# every module that holds declarations with leanchecker, print the axioms of every theorem, scan the
# sources for anything that would weaken a check. Outputs: build.<module>.out, leanchecker.<module>.out,
# replay.out, axioms_all.out, verify.out (when run as ./verify.sh > verify.out 2>&1).
set -u
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-1}
LOCK=${LEAN_LOCK:-/tmp/lean.lock}
cd "$(dirname "$0")" || exit 1
status=0
run() { flock "$LOCK" "$@"; }
echo "=== versions"; cat lean-toolchain; run lean --version; grep -A2 '"name": "mathlib"' lake-manifest.json | head -3; grep '"rev"' lake-manifest.json | head -1
mods="Transformer.ExpFix Transformer.Program Transformer.Logits Transformer.Compose Transformer.Raw"
echo "=== build, one module per lake call, start $(date -u +%FT%TZ)"
for m in $mods; do
  s=$(date +%s); run lake build "$m" > "build.$m.out" 2>&1; b=$?; e=$(date +%s)
  echo "build $m exit $b in $((e-s)) s: $(grep -E 'Build completed|error' "build.$m.out" | head -2 | tr '\n' ' ')"
  [ $b -eq 0 ] || status=1
done
run lake build Transformer > build.Transformer.out 2>&1; rb=$?; [ $rb -eq 0 ] || status=1; echo "build root exit $rb : $(grep -E 'Build completed|error' build.Transformer.out | head -1)"
echo "=== source scan (must be empty): sorry, native_decide, axiom, opaque, implemented_by, extern, skipKernelTC"
../lean/scan_sources.sh Transformer/*.lean Transformer.lean > scan.out 2>&1
sc=$?; cat scan.out; echo "source scan exit $sc"
if [ "$sc" -eq 0 ]; then echo "none found"; else status=1; fi
echo "=== leanchecker replay of every module with declarations (the root only imports), start $(date -u +%FT%TZ)"
: > replay.out
for m in $mods; do
  s=$(date +%s)
  if run lake env leanchecker "$m" > "leanchecker.$m.out" 2>&1; then r=OK; else r=FAIL; status=1; fi
  e=$(date +%s); echo "$r   $m ($((e-s)) s)" | tee -a replay.out
done
nok=$(grep -c '^OK' replay.out); echo "replayed $nok of 5 modules, end $(date -u +%FT%TZ)"; [ "$nok" -eq 5 ] || status=1
echo "=== axioms"
run lake env lean axioms_all.lean > axioms_all.out 2>&1; arc=$?; cat axioms_all.out; echo "axioms lean exit $arc"; [ $arc -eq 0 ] || status=1
nall=$(grep -cE "depends on axioms|does not depend on any axioms" axioms_all.out)
nstd=$(grep -cE "depends on axioms: \[(propext, Classical.choice, Quot.sound|propext, Quot.sound|propext|Quot.sound|Classical.choice|propext, Classical.choice|Classical.choice, Quot.sound)\]$|does not depend on any axioms" axioms_all.out)
nthm=$(grep -c "^#print axioms" axioms_all.lean)
echo "$nstd of $nall theorems use only standard axioms or none ($nthm asked)"; [ "$nstd" -eq "$nall" ] && [ "$nall" -eq "$nthm" ] || status=1
echo "=== done $(date -u +%FT%TZ), exit $status"; exit $status

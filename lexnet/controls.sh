#!/usr/bin/env bash
# Negative control: change one head weight (head[8][5] 9.0 -> 7.5), regenerate the Lean with the same generator,
# and compile the UNCHANGED Reference.lean, the Pilot.lean generated for the mutant, and the unchanged Bwd.lean.
# Accepted only if exactly the first two exit 0 and Bwd.lean exits 1 with exactly one error, at lean/Bwd.lean:57:6,
# Lean's `decide ... is false` diagnostic (check_control.py).  LEXNET_WORK is a parent directory, never wiped;
# a new private child is created in it (see verify.sh).
set -euo pipefail
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
command -v lean >/dev/null 2>&1 || { echo "FAIL: 'lean' not found on PATH. Install the toolchain pinned in lean-toolchain ($(cat "$HERE/lean-toolchain")) with elan and put its bin directory on PATH." >&2; exit 2; }
want=$(sed 's/^leanprover\/lean4:v//' "$HERE/lean-toolchain")
have=$(lean --version | sed -n 's/^Lean (version \([^,]*\),.*/\1/p')
[ "$want" = "$have" ] || { echo "FAIL: lean $have on PATH, lean-toolchain pins $want" >&2; exit 2; }
if [ -n "${LEXNET_WORK:-}" ]; then
  mkdir -p -- "$LEXNET_WORK"
  PARENT=$(cd "$LEXNET_WORK" && pwd -P)
else
  PARENT=$(cd "$(mktemp -d)" && pwd -P)
fi
case "$PARENT/" in
  "$HERE"/*) echo "FAIL: LEXNET_WORK ($PARENT) is the package directory or inside it; choose a directory outside $HERE" >&2; exit 2;;
esac
WORK=$(mktemp -d "$PARENT/run.XXXXXX")
cd "$HERE"
echo "run directory: $WORK"
python3 -B make_mutants.py "$WORK" head
M="$WORK/mutant-head"
cp lean/Reference.lean lean/Bwd.lean lean/Proof.inc "$M/lean/"
export LEAN_PATH="$M" LEAN_NUM_THREADS=4
exits=()
for m in Reference Pilot; do
  rc=0; (cd "$M" && lean -j4 -o "lean/$m.olean" "lean/$m.lean") > "$M/$m.log" 2>&1 || rc=$?
  echo "mutant $m exit=$rc"; exits+=("$rc")
done
rc=0; (cd "$M" && lean -j4 -o "lean/Bwd.olean" "lean/Bwd.lean") > "$M/Bwd.log" 2>&1 || rc=$?
echo "mutant Bwd exit=$rc"
python3 -B check_control.py "${exits[@]}" -- "$rc" "$M/Bwd.log"

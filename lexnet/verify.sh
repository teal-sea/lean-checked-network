#!/usr/bin/env bash
# Fail-closed verification of lexnet_correct.  Needs: bash, python3 (stdlib only), the Lean toolchain named in
# lean-toolchain on PATH (lean, and leanchecker in the same toolchain).  At most 4 Lean threads, one compiler
# at a time.
#   ./verify.sh            default: input digests, generator equality, clean sequential build of the theorem
#                          closure (17 modules plus Axioms.lean = 18 compiler runs), exact axiom inventory,
#                          leanchecker --fresh lean.Full
#   ./controls.sh          separate: changed-weight negative control
# LEXNET_WORK, if set, is a PARENT directory (created if missing, never wiped); every run uses a new private
# child run.XXXXXX inside it.  A parent that is, or lies inside, this package directory is refused.
# Build products go to the run directory; the generators run with python -I -B so no bytecode is written.
# The Lean toolchain, OS, Python and the weight parser exact.py are trusted; digests detect drift only.
set -euo pipefail
START_PWD=$PWD
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
MODULES="Reference Units Pilot NetExtra Hash Flags Fwd0 Fwd1a Fwd1b Fwd1c Fwd1d Fwd1 Fwd2 Fwd3a Bwd Fwd3 Full"

# checks that need no directory
command -v lean >/dev/null 2>&1 || { echo "FAIL: 'lean' not found on PATH. Install the toolchain pinned in lean-toolchain ($(cat "$HERE/lean-toolchain")) with elan and put its bin directory on PATH." >&2; exit 2; }
want=$(sed 's/^leanprover\/lean4:v//' "$HERE/lean-toolchain")
have=$(lean --version | sed -n 's/^Lean (version \([^,]*\),.*/\1/p')
[ "$want" = "$have" ] || { echo "FAIL: lean $have on PATH, lean-toolchain pins $want" >&2; exit 2; }
BIN="$(lean --print-prefix)/bin"
[ -x "$BIN/leanchecker" ] || { echo "FAIL: leanchecker not found in $BIN (it ships with the pinned toolchain)" >&2; exit 2; }

# private run directory under a resolved parent
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
echo "== 1. pinned inputs, accepted sources, generators"
python3 -B generate.py --check

echo "== 2. clean sequential build of the theorem closure"
mkdir -p "$WORK/lean" "$WORK/logs"
cp lean/*.lean lean/Proof.inc "$WORK/lean/"
export LEAN_PATH="$WORK" LEAN_NUM_THREADS=4
for m in $MODULES Axioms; do
  start=$(date +%s)
  rc=0
  (cd "$WORK" && lean -j4 -o "lean/$m.olean" "lean/$m.lean") > "$WORK/logs/$m.log" 2>&1 || rc=$?
  echo "$m exit=$rc wall=$(( $(date +%s) - start ))s"
  if [ "$rc" -ne 0 ]; then cat "$WORK/logs/$m.log" >&2; echo "FAIL: $m" >&2; exit 1; fi
done

echo "== 3. axiom inventory"
python3 -B check_axioms.py "$WORK/logs/Axioms.log"

echo "== 4. leanchecker --fresh lean.Full (Lean's kernel replay, scrubbed environment)"
start=$(date +%s)
mkdir -p "$WORK/home" "$WORK/tmp"
rc=0
env -i PATH="$BIN:/usr/bin:/bin" HOME="$WORK/home" TMPDIR="$WORK/tmp" LEAN_NUM_THREADS=2 LEAN_PATH="$WORK" \
  "$BIN/leanchecker" --fresh lean.Full > "$WORK/logs/leanchecker.log" 2>&1 || rc=$?
echo "leanchecker exit=$rc wall=$(( $(date +%s) - start ))s"
if [ "$rc" -ne 0 ]; then cat "$WORK/logs/leanchecker.log" >&2; echo "FAIL: leanchecker" >&2; exit 1; fi
echo "logs kept in $WORK/logs"
echo "VERIFY PASS"

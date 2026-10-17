#!/usr/bin/env bash
# Cheap regression for the smoke harness: scan_sources.sh must give 0 clean, 1 forbidden, 2 missing file; and
# the gates in smoke.sh / ../mathlib/verify.sh that earlier reviews found open must be present in the source.
cd "$(dirname "$0")" || exit 1
t=$(mktemp -d "${TMPDIR:-.}/transformer-harness.XXXXXX") || exit 1
fail=0
printf 'def a := 1\n' > "$t/clean.lean"; printf 'theorem x : True := by sorry\n' > "$t/bad.lean"
check() { # name expected actual
  if [ "$2" = "$3" ]; then echo "ok   $1"; else echo "FAIL $1: expected $2 got $3"; fail=1; fi
}
./scan_sources.sh "$t/clean.lean" > /dev/null; check scan-clean 0 $?
./scan_sources.sh "$t/clean.lean" "$t/bad.lean" > /dev/null; check scan-forbidden 1 $?
./scan_sources.sh "$t/clean.lean" "$t/missing.lean" > /dev/null 2>&1; check scan-missing-file 2 $?
./scan_sources.sh "$t/bad.lean" "$t/missing.lean" > /dev/null 2>&1; check scan-missing-wins-over-hit 2 $?
# the patterns are literal shell source text to look for in smoke.sh, so they must not be expanded here
# shellcheck disable=SC2016
check smoke-no-status-reset 0 "$(grep -c 's0=\$status\|status=\$s0' smoke.sh)"
# shellcheck disable=SC2016
check verify-axioms-exit-gated 1 "$(grep -c 'arc=\$?' ../mathlib/verify.sh)"
../mathlib/sync_core.sh --check > /dev/null; check core-copy-in-sync 0 $?
# the instrumented smoke must keep its evidence hooks: a signal trap, a streamed monitor, per-gate timeouts, split gates
for pat in "trap 'on_signal TERM" "^mon 2>&1 | tee" "timeout -s TERM" "gate build_weights" "gate build_table" "gate build_row0" "gate build_slice " "gate build_cols" "build_b_" "sha256sum -c W.sha256"; do
  check "smoke-has:$pat" 1 "$(grep -c -- "$pat" smoke.sh | awk '{print ($1>0)}')"
done
# the order that makes the slice a gate: BoundsLib, then the slice, then the other bound modules, Table, and row 0 last
lineof() { grep -n -- "$1" smoke.sh | head -1 | cut -d: -f1; }
ordered=1; prev=0
for pat in "gate build_lib" "gate build_slice " "gate build_data" 'gate "build_b_' "gate build_table" "gate build_row0"; do
  n=$(lineof "$pat"); if [ -z "$n" ] || [ "$n" -le "$prev" ]; then ordered=0; fi; prev=${n:-0}
done
check smoke-slice-before-full-bounds-before-row0 1 "$ordered"
# the Table assembly must not evaluate the tables: no `decide` over tablesOk itself, no simp/unfold of tab or bnd
check table-no-monolithic-decide 0 "$(grep -c 'tablesOk tab bnd = true := by' Transformer/Net/Table.lean)"
"${PYTHON:-python3}" test_pair_harness.py || fail=1
exit $fail

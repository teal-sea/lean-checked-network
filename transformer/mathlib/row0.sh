#!/usr/bin/env bash
# Free standard public Actions; serial stable ROW0/113 only.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
case "$LEAN_NUM_THREADS" in 1|2) ;; *) echo 'ROW0 status=FAIL: only 1 or 2 Lean threads'; exit 1;; esac
cd "$(dirname "$0")"
# Whole runner has a bounded deadline as well as each individual Lean command.
exec timeout -s TERM -k 20 6500 python3 -W error row0_runner.py "$@"

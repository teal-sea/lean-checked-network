#!/usr/bin/env bash
# Extreme last-head/token/position V/O and TU boundary after accepted O/U/CU; all production work remains in public manual Actions.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
case "$LEAN_NUM_THREADS" in 1|2) ;; *) echo 'only 1 or 2 Lean threads'; exit 1;; esac
cd "$(dirname "$0")"
export TMPDIR="$PWD/rawvoboundary-tmp"
mkdir -p "$TMPDIR"
exec /usr/bin/time -v -o rawvoboundary-total.time timeout -s TERM -k 10 3300 \
  python3 -B -W error rawvoboundary_runner.py "$@"

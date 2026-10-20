#!/usr/bin/env bash
# Bounded shared split V/O basis range after accepted O/U/CU; all production work remains in public manual Actions.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
case "$LEAN_NUM_THREADS" in 1|2) ;; *) echo 'only 1 or 2 Lean threads'; exit 1;; esac
cd "$(dirname "$0")"
export TMPDIR="$PWD/rawvorange-tmp"
mkdir -p "$TMPDIR"
exec /usr/bin/time -v -o rawvorange-total.time timeout -s TERM -k 10 3300 \
  python3 -B -W error rawvorange_runner.py "$@"

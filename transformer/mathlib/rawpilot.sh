#!/usr/bin/env bash
# One raw TI site, free public standard Actions only, serial builds/replays.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
case "$LEAN_NUM_THREADS" in 1|2) ;; *) echo 'RAW PILOT FAIL: only 1 or 2 Lean threads'; exit 1;; esac
cd "$(dirname "$0")"
export TMPDIR="$PWD/rawpilot-tmp"
mkdir -p "$TMPDIR"
exec /usr/bin/time -v -o rawpilot-total.time timeout -s TERM -k 10 3600 python3 -W error rawpilot_runner.py

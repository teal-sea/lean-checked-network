#!/usr/bin/env bash
# One packed raw TI site. Public standard Actions only; no artifact restore.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
case "$LEAN_NUM_THREADS" in 1|2) ;; *) echo 'RAW PACKED FAIL: only 1 or 2 Lean threads'; exit 1;; esac
cd "$(dirname "$0")"
export TMPDIR="$PWD/rawpacked-tmp"
mkdir -p "$TMPDIR"
exec /usr/bin/time -v -o rawpacked-total.time timeout -s TERM -k 10 6600 python3 -W error rawpacked_runner.py

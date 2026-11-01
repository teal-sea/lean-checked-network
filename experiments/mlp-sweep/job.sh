#!/bin/bash
# One sweep job on a box: KIND NAME ARGS...  (KIND sq: circle-curve/train_ckpt2.py + analyze_curve.py,
# relu: mlp-sweep/train_act.py relu + analyze_act.py, tf: transformer-curve/train_curve.py + reduce.py +
# probe_sum_part.py). One core per job; run_sweep.sh runs four at a time.
set -u
kind=$1; name=$2; shift 2
PY=~/tc/venv/bin/python
CC=~/tc/repo/experiments/circle-curve
MS=~/tc/repo/experiments/mlp-sweep
TC=~/tc/repo/experiments/transformer-curve
d=~/tc/out/$name; mkdir -p "$d"
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
echo "=== $name start $(date -u +%H:%M:%S)" >> ~/tc/out/progress.txt
t0=$(date +%s)
case $kind in
  sq)   $PY $CC/train_ckpt2.py "$@" "$d" > "$d/train.log" 2>&1 && $PY $CC/analyze_curve.py "$d" > "$d/analyze.log" 2>&1 ;;
  relu) $PY $MS/train_act.py relu "$@" "$d" > "$d/train.log" 2>&1 && $PY $MS/analyze_act.py "$d" > "$d/analyze.log" 2>&1 ;;
  tf)   $PY $TC/train_curve.py "$d" "$@" --threads 1 > "$d/train.log" 2>&1 \
          && $PY $TC/reduce.py "$d"/ckpt_*.npz > "$d/reduce.jsonl" 2> "$d/reduce.log" \
          && $PY $TC/probe_sum_part.py "$d"/ckpt_*.npz > "$d/probe.jsonl" 2> "$d/probe.log" ;;
esac
rc=$?
echo "=== $name exit $rc after $(( $(date +%s) - t0 )) s" >> ~/tc/out/progress.txt

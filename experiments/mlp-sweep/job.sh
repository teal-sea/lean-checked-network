#!/bin/bash
# One sweep job on a box: KIND NAME ARGS...  (KIND sq: circle-curve/train_ckpt2.py + analyze_curve.py,
# relu: mlp-sweep/train_act.py relu + analyze_act.py, sqe/relue: the same with one VAR=value
# environment setting first (SHUFFLE_LABELS=1, EARLY=1), tf: transformer-curve/train_curve.py + reduce.py +
# probe_sum_part.py), gen: mlp-sweep/train_gen.py + analyze_gen.py with '+'-joined VAR=value settings first;
# fourth batch: gene (gen + analyze_even.py), genq (gen + analyze_act.py, the integer projection),
# acte (train_act.py + analyze_act.py with '+'-joined settings). One core per job; four at a time.
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
  sqe)  ev=$1; shift; env "$ev" $PY $CC/train_ckpt2.py "$@" "$d" > "$d/train.log" 2>&1 && $PY $CC/analyze_curve.py "$d" > "$d/analyze.log" 2>&1 ;;
  relue) ev=$1; shift; env "$ev" $PY $MS/train_act.py relu "$@" "$d" > "$d/train.log" 2>&1 && $PY $MS/analyze_act.py "$d" > "$d/analyze.log" 2>&1 ;;
  gen)  IFS='+' read -ra evs <<< "$1"; shift; env "${evs[@]}" $PY $MS/train_gen.py "$@" "$d" > "$d/train.log" 2>&1 && $PY $MS/analyze_gen.py "$d" > "$d/analyze.log" 2>&1 ;;
  gene) IFS='+' read -ra evs <<< "$1"; shift; env "${evs[@]}" $PY $MS/train_gen.py "$@" "$d" > "$d/train.log" 2>&1 && $PY $MS/analyze_gen.py "$d" > "$d/analyze.log" 2>&1 \
          && $PY $MS/analyze_even.py "$d" > "$d/even.log" 2>&1 ;;
  genq) IFS='+' read -ra evs <<< "$1"; shift; env "${evs[@]}" $PY $MS/train_gen.py "$@" "$d" > "$d/train.log" 2>&1 && $PY $MS/analyze_gen.py "$d" > "$d/analyze.log" 2>&1 \
          && $PY $MS/analyze_act.py "$d" > "$d/analyze_int.log" 2>&1 ;;
  acte) IFS='+' read -ra evs <<< "$1"; shift; env "${evs[@]}" $PY $MS/train_act.py "$@" "$d" > "$d/train.log" 2>&1 && $PY $MS/analyze_act.py "$d" > "$d/analyze.log" 2>&1 ;;
  tf)   $PY $TC/train_curve.py "$d" "$@" --threads 1 > "$d/train.log" 2>&1 \
          && $PY $TC/reduce.py "$d"/ckpt_*.npz > "$d/reduce.jsonl" 2> "$d/reduce.log" \
          && $PY $TC/probe_sum_part.py "$d"/ckpt_*.npz > "$d/probe.jsonl" 2> "$d/probe.log" ;;
esac
rc=$?
echo "=== $name exit $rc after $(( $(date +%s) - t0 )) s" >> ~/tc/out/progress.txt

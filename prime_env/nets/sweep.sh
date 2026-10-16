#!/usr/bin/env bash
# Train small networks with the repo's train.py (copied unchanged) and record which froze to
# a network that is right on every pair. Output: nets/runs/p<P>_h<H>_s<SEED>.npz and sweep.log
set -u
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
cd "$(dirname "$0")"
mkdir -p runs
: > sweep.log
for p in 5 7 11 13 17 19 23; do
  for H in 8 16 32; do
    for seed in 0 1 2; do
      out=runs/p${p}_h${H}_s${seed}.npz
      t0=$(date +%s.%N)
      python3 train.py $p $H $seed 1e-2 0.5 0.7 2000 $out 2> runs/p${p}_h${H}_s${seed}.err
      t1=$(date +%s.%N)
      last=$(grep "frozen integer network" runs/p${p}_h${H}_s${seed}.err | tail -1)
      printf 'p=%s H=%s seed=%s %.1fs :: %s\n' $p $H $seed $(echo "$t1 - $t0" | bc) "$last" | tee -a sweep.log
    done
  done
done
echo SWEEP_DONE | tee -a sweep.log

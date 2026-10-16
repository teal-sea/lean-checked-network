#!/usr/bin/env bash
# Usage: sweep2.sh TAG WD FRAC STEPS   (train.py copied unchanged from the repo)
set -u
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
cd "$(dirname "$0")"
tag=$1; wd=$2; frac=$3; steps=$4
mkdir -p runs_$tag
log=sweep_$tag.log; : > $log
for p in 5 7 11 13 17 19 23; do
  for H in 8 16 32; do
    for seed in 0 1 2; do
      out=runs_$tag/p${p}_h${H}_s${seed}.npz
      t0=$(date +%s.%N)
      python3 train.py $p $H $seed 1e-2 $wd $frac $steps $out 2> runs_$tag/p${p}_h${H}_s${seed}.err
      t1=$(date +%s.%N)
      last=$(grep "frozen integer network" runs_$tag/p${p}_h${H}_s${seed}.err | tail -1)
      printf 'p=%s H=%s seed=%s %.1fs :: %s\n' $p $H $seed $(echo "$t1 - $t0" | bc) "$last" >> $log
    done
  done
done
echo SWEEP_DONE >> $log

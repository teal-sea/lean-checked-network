#!/bin/bash
# The first five Adam steps, checkpointed at every step, for several widths and seeds (2026-11-01).
# Rule fixed before running: for each (act, H, seed), the first step at which the rounded one-wave
# projection is wrong on 0 pairs (analyze_act.py's circle_wrong), and whether it stays 0 through step 5.
set -u
PY=~/tc/venv/bin/python; MS=~/tc/repo/experiments/mlp-sweep; out=~/tc/out/first_steps; mkdir -p $out
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 EXTRA_STEPS=1,2,3,4,5
for act in sq relu; do for H in 256 512 1024 2048; do for seed in 0 1 2; do
  d=$out/${act}_H${H}_s${seed}
  nice -n 5 $PY $MS/train_act.py $act 97 $H $seed 1e-2 0.0 0.30 5 $d > $d.train.log 2>&1
  nice -n 5 $PY $MS/analyze_act.py $d > $d.analyze.log 2>&1
  echo "== $act H $H seed $seed"; grep -E "^step +[0-5] " $d.analyze.log | cut -c1-90
done; done; done
touch $out/DONE

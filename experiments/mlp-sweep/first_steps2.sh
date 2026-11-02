#!/bin/bash
# Generality of the one-step result (2026-11-01, rule fixed before running): x^2 MLP, weight decay 0,
# lr 0.01, checkpoints at steps 1, 2, 3. For each (p, frac, H, seed): the first step at which the
# rounded one-wave projection is wrong on 0 pairs. Win: exact at step 1 for every seed at some width,
# for every modulus and fraction tried.
set -u
PY=~/tc/venv/bin/python; MS=~/tc/repo/experiments/mlp-sweep; out=~/tc/out/first_steps2; mkdir -p $out
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 EXTRA_STEPS=1,2,3
run() {  # p frac H seed
  d=$out/p$1_f$2_H$3_s$4
  nice -n 5 $PY $MS/train_act.py sq $1 $3 $4 1e-2 0.0 $2 3 $d > $d.train.log 2>&1
  nice -n 5 $PY $MS/analyze_act.py $d > $d.analyze.log 2>&1
  echo "== p $1 frac $2 H $3 seed $4: $(grep -E '^step +[1-3] ' $d.analyze.log | head -3 | sed -E 's/.*net wrong +([0-9]+) \| circle wrong +([0-9]+).*/net \1 circle \2/' | tr '\n' ';')"
}
for p in 31 61 113 127 257; do for H in 1024 2048; do for s in 0 1 2; do run $p 0.30 $H $s; done; done; done
for f in 0.15 0.50; do for H in 1024 2048; do for s in 0 1 2; do run 97 $f $H $s; done; done; done
touch $out/DONE

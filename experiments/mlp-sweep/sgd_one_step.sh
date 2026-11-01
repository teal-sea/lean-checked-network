#!/bin/bash
# One plain gradient-descent step (2026-11-01). x^2, p 97, frac 0.3, wd 0, OPT=sgd. Rule fixed before
# running: for H in {512, 1024, 2048} and lr = c * H with c in {0.3, 1, 3}, seeds 0-2, report the
# projection's wrong count after exactly one step (and two). Win: some c gives 0 after ONE step for
# every seed at every width (a single GD step with step size proportional to width).
set -u
PY=~/tc/venv/bin/python; MS=~/tc/repo/experiments/mlp-sweep; out=~/tc/out/sgd_one_step; mkdir -p $out
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 OPT=sgd EXTRA_STEPS=1,2
for H in 512 1024 2048; do for c in 0.3 1 3; do for s in 0 1 2; do
  lr=$(python3 -c "print($c * $H)")
  d=$out/H${H}_c${c}_s$s
  nice -n 5 $PY $MS/train_gen.py sq 97 $H $s $lr 0.0 0.30 2 $d > $d.train.log 2>&1
  echo "H $H c $c lr $lr seed $s | $(nice -n 5 $PY $MS/analyze_gen.py $d | grep -E '^step +[12] ' | sed -E 's/ +/ /g; s/sq net wrong/net/; s/projection wrong/proj/; s/\| acc.*//' | tr '\n' ';')"
done; done; done
touch $out/DONE

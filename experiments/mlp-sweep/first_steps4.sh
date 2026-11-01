#!/bin/bash
# How often is one Adam step enough? (2026-11-01, rule fixed before running.) x^2, p 97, frac 0.3,
# lr 0.01, wd 0, checkpoints at steps 1 and 2; H in {768, 1024, 1536, 2048}, seeds 0-19. Report per H
# the number of seeds whose rounded one-wave projection is wrong on 0 pairs at step 1 (and at step 2).
set -u
PY=~/tc/venv/bin/python; MS=~/tc/repo/experiments/mlp-sweep; out=~/tc/out/first_steps4; mkdir -p $out
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 EXTRA_STEPS=1,2
for H in 768 1024 1536 2048; do for s in $(seq 0 19); do
  d=$out/H${H}_s$s
  nice -n 5 $PY $MS/train_act.py sq 97 $H $s 1e-2 0.0 0.30 2 $d > $d.train.log 2>&1
  nice -n 5 $PY $MS/analyze_act.py $d > $d.analyze.log 2>&1
  echo "H $H seed $s $(grep -E '^step +[12] ' $d.analyze.log | head -2 | awk '{for(i=1;i<=NF;i++) if($i=="circle"){printf "step%s:%s net:%s ", $2, $(i+2), $6; break}}')"
done; done
touch $out/DONE

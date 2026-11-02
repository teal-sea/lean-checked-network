#!/bin/bash
# Learning-rate scaling of the first exact step (2026-11-01). Prediction fixed before running, from
# the first-order argument (one update factor times two initialization factors is phase-aligned for
# a + b; the projection's signal grows like t * lr * H against initialization noise): the first step
# t* at which the one-wave projection is wrong on 0 pairs satisfies t* * lr * H ~ 10 (the observed
# value at lr 0.01: H 256 -> 4 steps, H 512 -> 2, H 1024 -> 1), i.e. t* = ceil(10.24 / (lr * H)) give
# or take one step, as long as the step stays small against the initialization (lr << 1/sqrt(H)).
set -u
PY=~/tc/venv/bin/python; MS=~/tc/repo/experiments/mlp-sweep; out=~/tc/out/first_steps3; mkdir -p $out
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 EXTRA_STEPS=1,2,3,4,5,6,7,8
run() {  # H lr seed
  d=$out/H$1_lr$2_s$3
  nice -n 5 $PY $MS/train_act.py sq 97 $1 $3 $2 0.0 0.30 8 $d > $d.train.log 2>&1
  nice -n 5 $PY $MS/analyze_act.py $d > $d.analyze.log 2>&1
  first=$(grep -E '^step +[1-8] ' $d.analyze.log | awk '{for(i=1;i<=NF;i++) if($i=="circle"){print $2, $(i+2); break}}' | awk '$2==0{print $1; exit}')
  pred=$(python3 -c "import math; print(math.ceil(10.24/($2*$1)))")
  echo "== H $1 lr $2 seed $3: predicted t* $pred, observed t* ${first:-none by 8} | $(grep -E '^step +[1-8] ' $d.analyze.log | head -8 | awk '{for(i=1;i<=NF;i++) if($i=="circle"){printf "%s:%s ", $2, $(i+2); break}}')"
}
for s in 0 1 2; do
  for cfg in "256 0.02" "256 0.04" "512 0.02" "512 0.005" "1024 0.005" "1024 0.0025" "2048 0.0025" "2048 0.00125"; do
    set -- $cfg; run $1 $2 $s
  done
done
touch $out/DONE

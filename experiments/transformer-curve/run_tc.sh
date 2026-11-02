#!/bin/bash
# On-box runner for the transformer curve (boat.dev default box, 4 vCPU / 8 GB, 2026-11-01).
# Usage: ./run_tc.sh "LANE1_JOBS" "LANE2_JOBS"; a lane is a space-separated list of
#        NAME:WD:SEED:SHUF:EPOCHS run one after another; the two lanes run side by side
#        (2 torch threads each), and each run gets a reduce.py follower (1 thread, nice 19).
# Expects ~/tc/repo/{transformer/train.py, transformer/runs/best.npz, experiments/transformer-curve/}.
# Writes ~/tc/out/NAME/ (checkpoints, curve.tsv, reduce.jsonl, DONE, REDUCED), ~/tc/out/progress.txt,
# ~/tc/out/calib_best.jsonl (reduce.py on the released grokked net, a check against the
# calibration done before the runs), ~/tc/out/ALL_DONE.
set -u
cd ~/tc
if [ ! -x venv/bin/python ]; then
  python3 -m venv venv && venv/bin/pip install -q numpy && venv/bin/pip install -q torch --index-url https://download.pytorch.org/whl/cpu
fi
PY=~/tc/venv/bin/python
TC=~/tc/repo/experiments/transformer-curve
mkdir -p out
echo "box $(hostname): $(nproc) cores, $(free -g | awk '/Mem/ {print $2}') GB, $($PY -c 'import torch, numpy; print("torch", torch.__version__, "numpy", numpy.__version__)')" > out/box.txt
lane() {
  for job in $1; do
    IFS=: read -r name wd seed shuf epochs <<< "$job"
    d=~/tc/out/$name; mkdir -p "$d"
    echo "=== $name start $(date -u +%H:%M:%S)" >> ~/tc/out/progress.txt
    ( OMP_NUM_THREADS=1 nice -n 19 $PY $TC/reduce.py --follow "$d" > "$d/reduce.log" 2>&1 ) &
    rp=$!
    OMP_NUM_THREADS=2 $PY $TC/train_curve.py "$d" --wd "$wd" --seed "$seed" --epochs "$epochs" \
      $( [ "$shuf" = 1 ] && echo --shuffle-labels ) > "$d/train.log" 2>&1
    echo "=== $name trained exit $? $(date -u +%H:%M:%S)" >> ~/tc/out/progress.txt
    wait $rp
    echo "=== $name reduced $(date -u +%H:%M:%S)" >> ~/tc/out/progress.txt
  done
}
( OMP_NUM_THREADS=1 nice -n 19 $PY $TC/reduce.py ~/tc/repo/transformer/runs/best.npz > out/calib_best.jsonl 2> out/calib_best.err ) &
lane "$1" &
l1=$!
lane "$2" &
l2=$!
wait $l1 $l2
touch ~/tc/out/ALL_DONE

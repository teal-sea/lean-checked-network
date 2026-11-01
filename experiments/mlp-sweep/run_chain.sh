#!/bin/bash
# Wait for the running sweep (SWEEP_DONE), then run a second job file the same way; touch SWEEP2_DONE.
set -u
while [ ! -f ~/tc/out/SWEEP_DONE ]; do sleep 30; done
grep -v '^#' "$1" | grep . | xargs -P 4 -L 1 bash ~/tc/repo/experiments/mlp-sweep/job.sh
touch ~/tc/out/SWEEP2_DONE

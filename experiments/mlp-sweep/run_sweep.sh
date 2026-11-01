#!/bin/bash
# Run every line of JOBFILE (KIND NAME ARGS...) through job.sh, four at a time; then touch SWEEP_DONE.
set -u
cd ~/tc
grep -v '^#' "$1" | grep . | xargs -P 4 -L 1 bash ~/tc/repo/experiments/mlp-sweep/job.sh
touch ~/tc/out/SWEEP_DONE

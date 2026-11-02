#!/bin/bash
# Run every line of JOBFILE through job.sh, four at a time, then touch ~/tc/out/FLAG.
set -u
grep -v '^#' "$1" | grep . | xargs -P 4 -L 1 bash ~/tc/repo/experiments/mlp-sweep/job.sh
touch ~/tc/out/$2

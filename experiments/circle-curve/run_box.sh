#!/bin/bash
# On-box sequential runner for seal_jobs.json (used on boat.dev trial boxes, 4 vCPU / 8 GB, 2026-10-31).
# Usage: [BUILD_JOBS=3] [REPLAY_JOBS=2] ./run_box.sh JOBNAME [JOBNAME...]
# Expects ~/seal/{repo (lean/, sweep/, experiments/circle-curve/), inputs/<job>.npz, negctl_src/} on the box;
# installs elan + the repo's toolchain and numpy on first run. Writes ~/seal/out/<job>/, <job>.log, progress.txt,
# <job>.DONE or .FAILED, and ALL_DONE at the end. An H 128 cell takes about 20 min (build 8, replay 11) with three
# Lean processes; an H 256 cell needs BUILD_JOBS=1 REPLAY_JOBS=1 in 8 GB (three processes were OOM-killed).
# Build the bundle with COPYFILE_DISABLE=1 on macOS: AppleDouble ._* files break the negative control's directory walk.
# Supersedes remote_seal.sh.
set -u
export PATH="$HOME/.elan/bin:$PATH"; export OMP_NUM_THREADS=1
BUILD_JOBS="${BUILD_JOBS:-3}"; REPLAY_JOBS="${REPLAY_JOBS:-2}"
cd ~/seal
TOOLCHAIN="$(cat repo/lean/lean-toolchain)"
if ! command -v lean >/dev/null; then curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain "$TOOLCHAIN" >/dev/null 2>&1; fi
export PATH="$HOME/.elan/bin:$PATH"
python3 -c "import numpy" 2>/dev/null || { python3 -m venv ~/seal/venv && ~/seal/venv/bin/pip install -q numpy; }
PY=$( [ -x ~/seal/venv/bin/python ] && echo ~/seal/venv/bin/python || echo python3 )
( cd repo && git init -q 2>/dev/null; git add -A >/dev/null 2>&1; git -c user.email=x@x -c user.name=x commit -qm seal >/dev/null 2>&1 ) || true
mkdir -p out
echo "box $(hostname): $(nproc) cores, $(free -g | awk '/Mem/ {print $2}') GB, $(lean --version)" > out/box.txt
cd repo/experiments/circle-curve
for name in "$@"; do
  start=$(date +%s); echo "=== $name start $(date -u +%H:%M:%S)" >> ~/seal/out/progress.txt
  kind=$($PY -c "import json,sys; j=[x for x in json.load(open('seal_jobs.json')) if x['name']==sys.argv[1]][0]; print(j['kind'], j.get('only') or '-', int(bool(j.get('pure_clock'))))" "$name")
  set -- $kind; k=$1; only=$2; pure=$3
  if [ "$k" = seal ]; then
    $PY seal_cell.py ~/seal/inputs/$name.npz ~/seal/out/$name --repo ~/seal/repo --jobs $REPLAY_JOBS --build-jobs $BUILD_JOBS $( [ "$pure" = 1 ] && echo --pure-clock ) > ~/seal/out/$name.log 2>&1
    rc=$?; $PY seal_verdict.py ~/seal/out/ >> ~/seal/out/$name.log 2>&1 || true
  else
    $PY seal_negative_control.py ~/seal/negctl_src ~/seal/out/$name --build-jobs $BUILD_JOBS --only $only > ~/seal/out/$name.log 2>&1; rc=$?
  fi
  rm -rf ~/seal/out/$name/lean/.lake ~/seal/out/$name/*/.lake 2>/dev/null
  [ $rc -eq 0 ] && touch ~/seal/out/$name.DONE || touch ~/seal/out/$name.FAILED
  echo "=== $name exit $rc after $(( $(date +%s) - start )) s" >> ~/seal/out/progress.txt
done
touch ~/seal/out/ALL_DONE

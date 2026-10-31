#!/bin/bash
# Run the seal jobs (seal_jobs.json) on a plain Linux box over ssh, the way the hermes-ovh grid ran.
# Usage: ./remote_seal.sh HOST [PARALLEL]     (PARALLEL defaults to cores / 4; each job uses ~4 cores, ~8 GB)
# Ships lean/, sweep/run_one.py, sweep/WrongSet.lean, this directory's scripts, seal_inputs/ and the
# sealed LONG cell (for the negative control) to HOST:~/seal; installs elan + the pinned toolchain if
# missing; runs every job; pulls the results back into seals_remote/<job>/ (no .lake).
set -euo pipefail
HOST="$1"; PAR="${2:-}"
HERE="$(cd "$(dirname "$0")" && pwd)"; REPO="$(cd "$HERE/../.." && pwd)"
TOOLCHAIN="$(cat "$REPO/lean/lean-toolchain")"
ssh "$HOST" 'mkdir -p ~/seal/repo/lean ~/seal/repo/sweep ~/seal/repo/experiments/circle-curve ~/seal/inputs ~/seal/out'
rsync -aq --exclude .lake "$REPO/lean/" "$HOST:~/seal/repo/lean/"
rsync -aq "$REPO/sweep/run_one.py" "$REPO/sweep/WrongSet.lean" "$HOST:~/seal/repo/sweep/"
rsync -aq "$HERE/seal_cell.py" "$HERE/Bridge.lean" "$HERE/seal_verdict.py" "$HERE/seal_negative_control.py" "$HERE/unmask.py" "$HERE/seal_jobs.json" "$HOST:~/seal/repo/experiments/circle-curve/"
rsync -aq "$HERE/seal_inputs/" "$HOST:~/seal/inputs/"
rsync -aq --exclude .lake "$HERE/seals/LONG_p97_H128_f0.30_wd0.1_s0/" "$HOST:~/seal/negctl_src/"
ssh "$HOST" bash -s "$TOOLCHAIN" "$PAR" <<'REMOTE'
set -euo pipefail
TOOLCHAIN="$1"; PAR="$2"
export PATH="$HOME/.elan/bin:$PATH"
if ! command -v lean >/dev/null; then curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain "$TOOLCHAIN" >/dev/null; fi
elan toolchain install "$TOOLCHAIN" >/dev/null 2>&1 || true
python3 -c "import numpy" 2>/dev/null || { python3 -m venv ~/seal/venv && ~/seal/venv/bin/pip install -q numpy; }
PY=$( [ -x ~/seal/venv/bin/python ] && echo ~/seal/venv/bin/python || echo python3 )
cd ~/seal/repo && git init -q 2>/dev/null && git add -A >/dev/null 2>&1 && git -c user.email=x@x -c user.name=x commit -qm seal >/dev/null 2>&1 || true
CORES=$(nproc); MEMGB=$(awk '/MemTotal/ {printf "%d", $2/1048576}' /proc/meminfo)
[ -z "$PAR" ] && PAR=$(( CORES / 4 )); [ "$PAR" -lt 1 ] && PAR=1
BJ=$(( CORES / PAR )); [ "$BJ" -gt 8 ] && BJ=8; MAXBJ=$(( MEMGB / PAR / 2 )); [ "$BJ" -gt "$MAXBJ" ] && BJ=$MAXBJ; [ "$BJ" -lt 1 ] && BJ=1
echo "box: $CORES cores, ${MEMGB} GB; $PAR jobs at a time, $BJ Lean processes each; $(lean --version)"
cd ~/seal/repo/experiments/circle-curve
$PY - "$PY" "$BJ" > ~/seal/jobs.txt <<'PYEOF'
import json, sys
py, bj = sys.argv[1], sys.argv[2]
for j in json.load(open('seal_jobs.json')):
    n = j['name']
    if j['kind'] == 'seal':
        print(f"{n}\t{py} seal_cell.py ~/seal/inputs/{n}.npz ~/seal/out/{n} --repo ~/seal/repo --jobs 2 --build-jobs {bj}" + (" --pure-clock" if j.get('pure_clock') else "") + f" > ~/seal/out/{n}.log 2>&1; {py} seal_verdict.py ~/seal/out/ >> ~/seal/out/{n}.log 2>&1 || true")
    else:
        print(f"{n}\t{py} seal_negative_control.py ~/seal/negctl_src ~/seal/out/{n} --build-jobs {bj} --only {j['only']} > ~/seal/out/{n}.log 2>&1 || true")
PYEOF
cut -f2 ~/seal/jobs.txt | nohup xargs -P "$PAR" -I{} bash -c '{}' > ~/seal/run.log 2>&1 &
echo "launched $(wc -l < ~/seal/jobs.txt) jobs in the background; logs in ~/seal/out/*.log"
REMOTE

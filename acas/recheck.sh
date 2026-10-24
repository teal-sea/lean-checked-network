#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
acas_root="$PWD"
export LEAN_NUM_THREADS=2 OMP_NUM_THREADS=2 OPENBLAS_NUM_THREADS=2
export XDG_RUNTIME_DIR="/run/user/$(id -u)"
export DBUS_SESSION_BUS_ADDRESS="unix:path=$XDG_RUNTIME_DIR/bus"
mkdir -p work
if [[ "${ACAS_RECHECK_UNIT:-}" != 1 ]]; then
  exec systemd-run --user --wait --pipe --slice=certcheck.slice \
    --unit="acas-recheck-$(date +%s)" -p MemoryMax=80G -p CPUAffinity=0-7 \
    -p "WorkingDirectory=$acas_root" /usr/bin/env "PATH=$PATH" \
    ACAS_RECHECK_UNIT=1 LEAN_NUM_THREADS=2 OMP_NUM_THREADS=2 \
    /bin/bash "$acas_root/recheck.sh"
fi
exec > >(tee -a work/recheck.log) 2>&1
python3 - <<'PY'
import shutil
if shutil.disk_usage('.').free < 45_000_000_000:
    raise SystemExit('The 45 GB disk reserve is not available')
PY
python3 gen/fetch_inputs.py
if [[ ! -x work/venv/bin/python ]]; then
  if command -v uv >/dev/null; then uv venv work/venv; else python3 -m venv work/venv; fi
fi
if command -v uv >/dev/null; then
  uv pip install --python work/venv/bin/python -r gen/requirements.txt
else
  work/venv/bin/python -m pip install -r gen/requirements.txt
fi
work/venv/bin/python -m pytest
python3 gen/regenerate.py --check
python3 gen/independent.py
(cd lean && lake update && lake exe cache get)
python3 gen/build.py --all --replay
python3 gen/audit.py
python3 gen/nanoda.py

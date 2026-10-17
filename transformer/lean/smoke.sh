#!/usr/bin/env bash
# Core-Lean smoke: build Transformer (Model, Fast, Equiv), BoundsLib, ONE representative bounds slice (a head of TI0), then the
# generated data, Weights, the remaining bound modules (one lake call each), Table (tables_ok assembled from them),
# Rows00 (the first row only) and the G column sums, as separately logged, separately timed gates. Never builds Net.AllInputs or the other 112 rows.
# Evidence survives a killed step: a resource line is streamed to the log every 3 s, every gate has its own timeout,
# and a SIGTERM/SIGINT trap prints the process table, the cgroup OOM counters and the kernel log before exiting.
set -u
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
cd "$(dirname "$0")" || exit 1
out=ci-out; mkdir -p "$out"
status=0

mon() { # one line per sample: time, MemAvailable MB, swap used MB, cgroup oom_kill count, top two processes by RSS
  while sleep 3; do
    printf 'mon %s avail=%sMB swap=%sMB oom_kill=%s top=%s\n' "$(date -u +%T)" \
      "$(awk '/MemAvailable/ {print int($2/1024)}' /proc/meminfo)" \
      "$(awk '/SwapTotal/ {t=$2} /SwapFree/ {f=$2} END {print int((t-f)/1024)}' /proc/meminfo)" \
      "$(awk '/^oom_kill / {print $2}' /sys/fs/cgroup/memory.events 2>/dev/null || echo na)" \
      "$(ps -eo rss,etimes,comm --sort=-rss | awk 'NR>1 && NR<4 {printf "%s:%dMB:%ss ", $3, $1/1024, $2}')"
  done
}
mon 2>&1 | tee -a "$out/monitor.log" &
montid=$!

dump() { # why: print what a post-mortem needs
  echo "=== dump ($1) $(date -u +%FT%TZ)"
  ps -eo pid,ppid,stat,rss,etimes,args --sort=-rss 2>&1 | cut -c1-200 | head -15
  echo "--- cgroup memory.events / memory.peak"; cat /sys/fs/cgroup/memory.events /sys/fs/cgroup/memory.peak 2>&1 | head -12
  echo "--- kernel log tail"; { sudo -n dmesg 2>&1 || dmesg 2>&1; } | tail -n 25
  echo "--- free"; free -m
}
# shellcheck disable=SC2329  # invoked by the traps below
on_signal() { dump "smoke.sh received $1"; kill "$montid" 2>/dev/null; exit "$2"; }
trap 'on_signal TERM 143' TERM
trap 'on_signal INT 130' INT
trap 'on_signal HUP 129' HUP

echo "=== versions"; cat lean-toolchain; lean --version; nproc; free -m | head -2
echo "=== monitor: cgroup memory.max $(cat /sys/fs/cgroup/memory.max 2>&1), data $(du -sk Transformer/Net/W | cut -f1) KB"

gate() { # name, timeout seconds, command...; wall time and peak RSS in ci-out/NAME.time, all output in ci-out/NAME.out and streamed
  local name=$1 secs=$2; shift 2
  echo "=== $name start $(date -u +%FT%TZ) (timeout ${secs}s)"
  /usr/bin/time -v -o "$out/$name.time" timeout -s TERM -k 20 "$secs" "$@" 2>&1 | tee "$out/$name.out" | grep -E --line-buffered "^(✔|✖|error|warning|trace|Build)" | cut -c1-240
  local rc=${PIPESTATUS[0]}
  echo "$name exit $rc; wall $(grep 'Elapsed' "$out/$name.time" 2>/dev/null | sed 's/.*): //'); max RSS KB $(grep 'Maximum resident' "$out/$name.time" 2>/dev/null | sed 's/.*: //')"
  [ "$rc" -eq 0 ] || { status=1; dump "$name exit $rc"; }
  return "$rc"
}

stop() { kill "$montid" 2>/dev/null; echo "=== done $(date -u +%FT%TZ), exit $status"; exit "$status"; }

echo "=== data provenance: the generated data files are byte-identical to the manifest (Net/W.sha256)"
(cd Transformer/Net && sha256sum -c W.sha256) > "$out/w-sha256.out" 2>&1 || { status=1; echo "W data differs from W.sha256"; }
tail -n 3 "$out/w-sha256.out"

gate build_core 600 lake build Transformer || { echo "core build failed, stopping"; stop; }
gate build_lib 600 lake build Transformer.BoundsLib || { echo "BoundsLib failed, stopping"; stop; }
# The representative slice: one head of TI0 (114 vectors of 512 entries, about 58,000 literals, a quarter of TI0 and a
# ninth of the whole table). Its data is built first as its own gate so the bound checks are timed apart from the data.
gate build_slice_data 900 lake build Transformer.Net.W.TI0_0 || { echo "slice data failed, stopping"; stop; }
gate build_slice 900 lake build Transformer.Net.B.TI0_0 || { echo "bounds slice failed, stopping before the other bound modules"; stop; }
data="Transformer.Net.W.TI0_1 Transformer.Net.W.TI0_2 Transformer.Net.W.TI0_3 Transformer.Net.W.TI1_0 Transformer.Net.W.TI1_1 Transformer.Net.W.TI1_2 Transformer.Net.W.TI1_3 Transformer.Net.W.TU0 Transformer.Net.W.TU1 Transformer.Net.W.Misc"
# shellcheck disable=SC2086
gate build_data 900 lake build $data || { echo "generated data failed, stopping"; stop; }
gate build_weights 600 lake build Transformer.Net.Weights || { echo "Weights failed, stopping"; stop; }
# The rest of the bounds modules, one lake call each (serial, so the peak memory is that of one module).
for m in TI0_1 TI0_2 TI0_3 TI1_0 TI1_1 TI1_2 TI1_3 TU0 TU1 Misc G; do
  gate "build_b_$m" 900 lake build "Transformer.Net.B.$m" || { echo "bounds module $m failed, stopping"; stop; }
done
gate build_table 600 lake build Transformer.Net.Table || { echo "tables_ok assembly failed, stopping"; stop; }
gate build_row0 1200 lake build Transformer.Net.Rows00 || { echo "row 0 failed, stopping"; stop; }
# G column sums: independent evidence, its failure does not hide the row-0 result above
cols_ok=0
if gate build_cols 900 lake build Transformer.Net.Cols; then cols_ok=1; fi

echo "=== source scan (must be empty): sorry, native_decide, axiom, opaque, implemented_by, extern, skipKernelTC"
./scan_sources.sh Transformer/Model.lean Transformer/Fast.lean Transformer/Equiv.lean Transformer/BoundsLib.lean Transformer/Net/Table.lean Transformer/Net/Cols.lean Transformer/Net/B/*.lean Transformer/Net/Rows00.lean Transformer.lean > "$out/scan.out" 2>&1; sc=$?
cat "$out/scan.out"
case $sc in 0) echo "none found" ;; 1) echo "forbidden construct found"; status=1 ;; *) echo "scan error $sc"; status=1 ;; esac
cat > "$out/axioms.lean" <<'LEAN'
import Transformer.Net.Rows00
#print axioms Transformer.fastCheck_correct
#print axioms Transformer.Net.tables_ok
#print axioms Transformer.Net.fast_0
LEAN
gate axioms 600 lake env lean "$out/axioms.lean"; cat "$out/axioms.out"
n=$(grep -cE "^.[^ ]+. (does not depend on any axioms|depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\])$" "$out/axioms.out")
echo "$n of 3 theorems on standard axioms or none"; [ "$n" -eq 3 ] || status=1
if [ "$cols_ok" -eq 1 ]; then
  cat > "$out/axioms_cols.lean" <<'LEAN'
import Transformer.Net.Cols
#print axioms Transformer.Net.colSums_ok
#print axioms Transformer.Net.G_length
LEAN
  gate axioms_cols 600 lake env lean "$out/axioms_cols.lean"; cat "$out/axioms_cols.out"
  n=$(grep -cE "^.[^ ]+. (does not depend on any axioms|depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\])$" "$out/axioms_cols.out")
  echo "$n of 2 column-sum theorems on standard axioms or none"; [ "$n" -eq 2 ] || status=1
else
  status=1; echo "column sums did not build, no axiom check for them"
fi
echo "=== leanchecker replay of Equiv and Rows00, both gating"
gate replay_equiv 600 lake env leanchecker Transformer.Equiv
gate replay_row0 1200 lake env leanchecker Transformer.Net.Rows00 || echo "row0 replay failed (gating: exit stays nonzero)"
stop

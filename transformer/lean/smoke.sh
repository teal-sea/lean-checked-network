#!/usr/bin/env bash
# Measured core gates. Pair modes stop before row0; full-row retains the row0 route.
# Pilot acceptance is only three literal checks, never fast_0 or all-input acceptance.
set -u
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
case "$LEAN_NUM_THREADS" in 1|2) ;; *) echo "LEAN_NUM_THREADS must be 1 or 2"; exit 2 ;; esac
mode=${CORE_MODE:-pair-pilot}
case "$mode" in pair-pilot|cached-pair-pilot|cached-support-pilot|full-row) ;; *) echo "unknown CORE_MODE: $mode"; exit 2 ;; esac
cd "$(dirname "$0")" || exit 1
out=ci-out; mkdir -p "$out"
status=0
printf 'source_sha=%s\nrun_id=%s\ncore_mode=%s\nlean_threads=%s\n' "${GITHUB_SHA:-local-fixture}" "${GITHUB_RUN_ID:-local-fixture}" "$mode" "$LEAN_NUM_THREADS" > "$out/SOURCE.txt"
printf '%s\n' "mode=$mode; running; row0 remains unproved; all-input acceptance unproved" > "$out/STATUS.txt"

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
echo "=== monitor: cgroup memory.max $(cat /sys/fs/cgroup/memory.max 2>&1)"

gate() { # name, timeout seconds, command...; wall time and peak RSS in ci-out/NAME.time, all output in ci-out/NAME.out and streamed
  local name=$1 secs=$2; shift 2
  echo "=== $name start $(date -u +%FT%TZ) (timeout ${secs}s)"
  /usr/bin/time -v -o "$out/$name.time" timeout -s TERM -k 20 "$secs" "$@" 2>&1 | tee "$out/$name.out" | grep -E --line-buffered "^(✔|✖|error|warning|trace|Build)" | cut -c1-240
  local rc=${PIPESTATUS[0]}
  echo "$name exit $rc; wall $(grep 'Elapsed' "$out/$name.time" 2>/dev/null | sed 's/.*): //'); max RSS KB $(grep 'Maximum resident' "$out/$name.time" 2>/dev/null | sed 's/.*: //')"
  [ "$rc" -eq 0 ] || {
    status=1
    echo "=== full failing output: $out/$name.out (retained without truncation)"
    cat "$out/$name.out"
    dump "$name exit $rc"
  }
  return "$rc"
}

stop() {
  if [ "$status" -ne 0 ]; then
    echo "mode=$mode; FAILED; row0/all-input acceptance not established by this run" > "$out/STATUS.txt"
  fi
  kill "$montid" 2>/dev/null; echo "=== done $(date -u +%FT%TZ), exit $status"; exit "$status"; }

# This early exit is a support-only acceptance boundary: no frozen inputs,
# code generation, table/bounds modules, pairs or rows are reached in this mode.
if [ "$mode" = cached-support-pilot ]; then
  gate build_core 120 lake build Transformer || stop
  gate build_cached 120 lake build Transformer.Cached || stop
  gate replay_cached 180 lake env leanchecker Transformer.Cached || stop
  gate build_cached_fixture 60 lake build Transformer.CachedFixture || stop
  gate replay_cached_fixture 180 lake env leanchecker Transformer.CachedFixture || stop
  /usr/bin/time -v -o "$out/cache_red.time" timeout -s TERM -k 20 60 lake env lean cache-red.lean > "$out/cache_red.out" 2>&1
  red_rc=$?
  if [ "$red_rc" -ne 1 ] || ! grep -q 'decide' "$out/cache_red.out"; then
    status=1; echo "altered packed-literal red control failed (exit $red_rc)"; stop
  fi
  echo 'Altered packed-literal kernel red control rejected as expected'
  gate support_scan 30 ./scan_sources.sh Transformer/Model.lean Transformer/Fast.lean Transformer/Equiv.lean Transformer/Cached.lean Transformer/CachedFixture.lean cache-red.lean || stop
  echo 'import Transformer.CachedFixture' > "$out/axioms.lean"
  expected=0
  for theorem in fastCheck_correct cachedHeadPk_map cachedFastCheck_pack cachedFastCheck_eq PackedTab.eq_of_fields packed_cons_of nth_pkI_map nth_pkI_map₂; do
    echo "#print axioms Transformer.$theorem" >> "$out/axioms.lean"
    expected=$((expected + 1))
  done
  for theorem in empty negative signed default_inner default_outer empty_vector arbitrary_indices; do
    echo "#print axioms Transformer.CachedFixture.$theorem" >> "$out/axioms.lean"
    expected=$((expected + 1))
  done
  gate axioms 120 lake env lean "$out/axioms.lean" || stop
  n=$(grep -cE "^.[^ ]+. (does not depend on any axioms|depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\])$" "$out/axioms.out")
  echo "$n of $expected theorems on standard axioms or none"
  [ "$n" -eq "$expected" ] || { status=1; stop; }
  gate replay_equiv 180 lake env leanchecker Transformer.Equiv || stop
  echo 'CACHED SUPPORT PILOT accepted; generic correspondence and edge fixtures only; frozen literals, cached pairs, row0 and all-input acceptance unproved by this run' | tee "$out/STATUS.txt"
  stop
fi

echo "=== data provenance: the generated data files are byte-identical to the manifest (Net/W.sha256)"
(cd Transformer/Net && sha256sum -c W.sha256) > "$out/w-sha256.out" 2>&1 || { status=1; echo "W data differs from W.sha256"; stop; }
tail -n 3 "$out/w-sha256.out"

gate build_core 600 lake build Transformer || { echo "core build failed, stopping"; stop; }
if [ "$mode" = cached-pair-pilot ]; then
  # Fail on symbolic support/edge fixtures before the expensive frozen-table work.
  gate build_cached 600 lake build Transformer.Cached || stop
  gate replay_cached 600 lake env leanchecker Transformer.Cached || stop
  gate build_cached_fixture 300 lake build Transformer.CachedFixture || stop
  gate replay_cached_fixture 300 lake env leanchecker Transformer.CachedFixture || stop
  # A changed packed literal must fail, with a decide diagnostic rather than a crash/timeout.
  /usr/bin/time -v -o "$out/cache_red.time" timeout -s TERM -k 20 60 lake env lean cache-red.lean > "$out/cache_red.out" 2>&1
  red_rc=$?
  if [ "$red_rc" -ne 1 ] || ! grep -q 'decide' "$out/cache_red.out"; then
    status=1; echo "altered packed-literal red control failed (exit $red_rc)"; stop
  fi
  echo 'Altered packed-literal kernel red control rejected as expected'
  gate cache_codegen 300 python3 gen_cached.py --out . || stop
  gate cache_codegen_repro 300 python3 gen_cached.py --out . --check || stop
fi
gate build_lib 600 lake build Transformer.BoundsLib || { echo "BoundsLib failed, stopping"; stop; }
# The representative slice: one head of TI0 (114 vectors of 512 entries, about 58,000 literals, a quarter of TI0 and a
# ninth of the whole table). Its data is built first as its own gate so the bound checks are timed apart from the data.
gate build_slice_data 900 lake build Transformer.Net.W.TI0_0 || { echo "slice data failed, stopping"; stop; }
gate build_slice 900 lake build Transformer.Net.B.TI0_0 || { echo "bounds slice failed, stopping before the other bound modules"; stop; }
data="Transformer.Net.W.TI0_1 Transformer.Net.W.TI0_2 Transformer.Net.W.TI0_3 Transformer.Net.W.TI1_0 Transformer.Net.W.TI1_1 Transformer.Net.W.TI1_2 Transformer.Net.W.TI1_3 Transformer.Net.W.TU0 Transformer.Net.W.TU1 Transformer.Net.W.Misc"
if [ "$mode" = cached-pair-pilot ]; then
  for module in $data; do
    gate "build_data_${module##*.}" 900 lake build "$module" || stop
  done
else
# shellcheck disable=SC2086
gate build_data 900 lake build $data || { echo "generated data failed, stopping"; stop; }
fi
gate build_weights 600 lake build Transformer.Net.Weights || { echo "Weights failed, stopping"; stop; }
# The rest of the bounds modules, one lake call each (serial, so the peak memory is that of one module).
for m in TI0_1 TI0_2 TI0_3 TI1_0 TI1_1 TI1_2 TI1_3 TU0 TU1 Misc G; do
  gate "build_b_$m" 900 lake build "Transformer.Net.B.$m" || { echo "bounds module $m failed, stopping"; stop; }
done
gate build_table 600 lake build Transformer.Net.Table || { echo "tables_ok assembly failed, stopping"; stop; }
# Independent column evidence runs before any pair or full row.
gate build_cols 900 lake build Transformer.Net.Cols || stop
if [ "$mode" = cached-pair-pilot ]; then
  # Dependency order is generated explicitly. Separate serial calls preserve unit time/RSS.
  while IFS= read -r module; do
    unit=${module#Transformer.Net.}
    gate "build_cache_$unit" 600 lake build "$module" || stop
    gate "replay_cache_$unit" 600 lake env leanchecker "$module" || stop
  done < "$out/cache-codegen/modules.txt"
  for pair in 0_0 0_112 96_73; do
    gate "build_cached_pair_$pair" 300 lake build "Transformer.Net.CachedPair$pair" || stop
  done
elif [ "$mode" = pair-pilot ]; then
  for pair in 0_0 0_112 96_73; do
    gate "build_pair_$pair" 300 lake build "Transformer.Net.Pair$pair" || stop
  done
else
  gate build_row0 1200 lake build Transformer.Net.Rows00 || stop
fi

echo "=== source scan (must be empty): forbidden trust constructs"
./scan_sources.sh Transformer/Model.lean Transformer/Fast.lean Transformer/Equiv.lean Transformer/BoundsLib.lean Transformer/Net/Table.lean Transformer/Net/Cols.lean Transformer/Net/B/*.lean Transformer/Net/Pair*.lean Transformer/Net/Rows00.lean Transformer.lean > "$out/scan.out" 2>&1
sc=$?; cat "$out/scan.out"
[ "$sc" -eq 0 ] || { status=1; stop; }
if [ "$mode" = cached-pair-pilot ]; then
  # Do not let a generated source escape the trust scan, including pair proof files.
  cache_sources=()
  while IFS= read -r source; do cache_sources+=("$source"); done < "$out/cache-codegen/sources.txt"
  ./scan_sources.sh Transformer/Cached.lean Transformer/CachedFixture.lean cache-red.lean "${cache_sources[@]}" > "$out/cache-scan.out" 2>&1
  sc=$?; cat "$out/cache-scan.out"
  [ "$sc" -eq 0 ] || { status=1; stop; }
fi

cat > "$out/axioms.lean" <<'LEAN'
import Transformer.Equiv
import Transformer.Net.Table
import Transformer.Net.Cols
LEAN
if [ "$mode" = cached-pair-pilot ]; then
  echo 'import Transformer.CachedFixture' >> "$out/axioms.lean"
  for pair in 0_0 0_112 96_73; do
    echo "import Transformer.Net.CachedPair$pair" >> "$out/axioms.lean"
  done
elif [ "$mode" = pair-pilot ]; then
  for pair in 0_0 0_112 96_73; do
    echo "import Transformer.Net.Pair$pair" >> "$out/axioms.lean"
  done
else
  echo 'import Transformer.Net.Rows00' >> "$out/axioms.lean"
fi
cat >> "$out/axioms.lean" <<'LEAN'
#print axioms Transformer.fastCheck_correct
#print axioms Transformer.Net.tables_ok
#print axioms Transformer.Net.colSums_ok
#print axioms Transformer.Net.G_length
LEAN
expected=4
if [ "$mode" = cached-pair-pilot ]; then
  for theorem in Transformer.cachedHeadPk_map Transformer.cachedFastCheck_pack Transformer.cachedFastCheck_eq Transformer.PackedTab.eq_of_fields Transformer.packed_cons_of Transformer.nth_pkI_map Transformer.nth_pkI_map₂; do
    echo "#print axioms $theorem" >> "$out/axioms.lean"
    expected=$((expected + 1))
  done
  for theorem in empty negative signed default_inner default_outer empty_vector arbitrary_indices; do
    echo "#print axioms Transformer.CachedFixture.$theorem" >> "$out/axioms.lean"
    expected=$((expected + 1))
  done
  # Every literal certificate and every ordinary assembly equality, plus the pilots.
  while IFS= read -r theorem; do
    echo "#print axioms $theorem" >> "$out/axioms.lean"
    expected=$((expected + 1))
  done < "$out/cache-codegen/axioms.txt"
elif [ "$mode" = pair-pilot ]; then
  for pair in 0_0 0_112 96_73; do
    echo "#print axioms Transformer.Net.pilot_$pair" >> "$out/axioms.lean"
  done
  expected=7
else
  echo '#print axioms Transformer.Net.fast_0' >> "$out/axioms.lean"
  expected=5
fi
gate axioms 600 lake env lean "$out/axioms.lean" || stop
if [ "$mode" = cached-pair-pilot ]; then
  tail -n 12 "$out/axioms.out"
else
  cat "$out/axioms.out"
fi
n=$(grep -cE "^.[^ ]+. (does not depend on any axioms|depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\])$" "$out/axioms.out")
echo "$n of $expected theorems on standard axioms or none"
[ "$n" -eq "$expected" ] || { status=1; stop; }
gate replay_equiv 600 lake env leanchecker Transformer.Equiv || stop
gate replay_table 600 lake env leanchecker Transformer.Net.Table || stop
gate replay_cols 900 lake env leanchecker Transformer.Net.Cols || stop
if [ "$mode" = cached-pair-pilot ]; then
  for pair in 0_0 0_112 96_73; do
    gate "replay_cached_pair_$pair" 300 lake env leanchecker "Transformer.Net.CachedPair$pair" || stop
  done
  echo 'CACHED PAIR PILOT accepted; row0 remains unproved; all-input acceptance unproved' | tee "$out/STATUS.txt"
elif [ "$mode" = pair-pilot ]; then
  for pair in 0_0 0_112 96_73; do
    gate "replay_pair_$pair" 300 lake env leanchecker "Transformer.Net.Pair$pair" || stop
  done
  echo 'PAIR PILOT accepted; row0 remains unproved; all-input acceptance unproved' | tee "$out/STATUS.txt"
else
  gate replay_row0 1200 lake env leanchecker Transformer.Net.Rows00 || stop
  echo 'Full-row route: row0 accepted; rows 1..112 and all-input acceptance unproved' | tee "$out/STATUS.txt"
fi
stop

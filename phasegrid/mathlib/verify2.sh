#!/usr/bin/env bash
# Stage 2 verification: build, replay every PhaseGrid module with leanchecker, print axioms, scan sources.
set -u
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")"
status=0
echo "=== versions"; cat lean-toolchain; lean --version; grep -A2 '"name": "mathlib"' lake-manifest.json | head -3; grep '"rev"' lake-manifest.json | head -1
echo "=== build start $(date -u +%FT%TZ)"
lake build > build.out 2>&1; b=$?; grep -E "✖|error|Build completed|sorry" build.out | head; echo "build exit $b"; [ $b -eq 0 ] || status=1
echo "=== source scan (must be empty): sorry, native_decide, axiom, opaque, implemented_by, extern, skipKernelTC"
grep -nE "sorry|native_decide|^\s*axiom |opaque |implemented_by|extern|skipKernelTC|decide \+native" PhaseGrid/*.lean PhaseGrid.lean && status=1 || echo "none found"
echo "=== Network.lean identical to the repository's?"
diff PhaseGrid/Network.lean ../../lean/LeanCheckedNetwork/Network.lean && echo "identical" || status=1
echo "=== replay every module with leanchecker, 2 at a time, start $(date -u +%FT%TZ)"
# The root module PhaseGrid only imports the others; replaying it re-checks every PhaseGrid module in one process
# (6.4 GB, OOM-killed on this machine), so each module is replayed once, on its own, as the first repository does.
mods="PhaseGrid.Network PhaseGrid.ListLemmas PhaseGrid.Trig PhaseGrid.Defs PhaseGrid.Score PhaseGrid.FullSet PhaseGrid.FullSetEven PhaseGrid.P7FullTables PhaseGrid.Close PhaseGrid.P7Link PhaseGrid.Open PhaseGrid.Cycle"
printf '%s\n' $mods | xargs -P ${JOBS:-1} -I{} sh -c 'if lake env leanchecker {} > leanchecker.{}.out 2>&1; then echo "OK   {}"; else echo "FAIL {}"; cat leanchecker.{}.out; fi' > replay.out
sort replay.out; nok=$(grep -c '^OK' replay.out); echo "replayed $nok of 12 modules, end $(date -u +%FT%TZ)"; [ "$nok" -eq 12 ] || status=1
echo "=== axioms"
cat > axioms_all.lean <<'LEAN'
import PhaseGrid
#print axioms PhaseGrid.octet
#print axioms PhaseGrid.realScore_eq
#print axioms PhaseGrid.waveSum_right
#print axioms PhaseGrid.waveSum_wrong
#print axioms PhaseGrid.abs_round_le
#print axioms PhaseGrid.neuron_bound
#print axioms PhaseGrid.intScore_close
#print axioms PhaseGrid.intScore_lt
#print axioms PhaseGrid.adds_mod_p
#print axioms PhaseGrid.adds_mod_p_of_gap
#print axioms PhaseGrid.sum_cos_range_eq_zero
#print axioms PhaseGrid.sum_cos_half
#print axioms PhaseGrid.adds_mod_p_full_odd
#print axioms PhaseGrid.sum_cos_even_le
#print axioms PhaseGrid.adds_mod_p_full_even
#print axioms PhaseGrid.adds_mod_p_full
#print axioms PhaseGrid.adds_mod_7_full
#print axioms PhaseGrid.adds_mod_113_full
#print axioms LeanCheckedNetwork.argmax_of_strict
#print axioms LeanCheckedNetwork.answer_ofFn
#print axioms PhaseGrid.abs_int_le_of_close
#print axioms PhaseGrid.neuron_bound_close
#print axioms PhaseGrid.intScoreT_close
#print axioms PhaseGrid.intScoreT_lt
#print axioms PhaseGrid.adds_mod_p_tables
#print axioms PhaseGrid.adds_mod_p_of_close_round
#print axioms PhaseGrid.cos_pi28
#print axioms PhaseGrid.sin_pi28
#print axioms PhaseGrid.double_bounds
#print axioms PhaseGrid.bounds_2pi7
#print axioms PhaseGrid.bounds_4pi7
#print axioms PhaseGrid.cos_theta_quarter
#print axioms PhaseGrid.E1_close
#print axioms PhaseGrid.E2_close
#print axioms PhaseGrid.W2_close
#print axioms PhaseGrid.gap123
#print axioms PhaseGrid.P7FullTables.adds_mod_7_by_theorem
#print axioms PhaseGrid.E1_round
#print axioms PhaseGrid.E2_round
#print axioms PhaseGrid.W2_round
#print axioms PhaseGrid.tablesMatchP7
#print axioms PhaseGrid.P7FullTables.adds_mod_7_by_full
#print axioms PhaseGrid.sum_cos_cycle_eq_zero
#print axioms PhaseGrid.expand_abc
#print axioms PhaseGrid.expand_phase
#print axioms PhaseGrid.sextet
#print axioms PhaseGrid.realScoreC_eq
#print axioms PhaseGrid.intScoreC_close
#print axioms PhaseGrid.intScoreC_lt
#print axioms PhaseGrid.adds_mod_p_cycle
#print axioms PhaseGrid.adds_mod_p_cycle_of_gap
#print axioms PhaseGrid.intScoreCT_close
#print axioms PhaseGrid.intScoreCT_lt
#print axioms PhaseGrid.adds_mod_p_cycle_tables
#print axioms PhaseGrid.adds_mod_p_cycle_full_odd
#print axioms PhaseGrid.adds_mod_p_cycle_full_even
#print axioms PhaseGrid.adds_mod_p_cycle_full
#print axioms PhaseGrid.adds_mod_113_cycle_full
#print axioms PhaseGrid.adds_mod_257_cycle_full
LEAN
lake env lean axioms_all.lean > axioms_all.out 2>&1; lrc=$?; cat axioms_all.out
# Fail closed: Lean must exit 0, print no error, and every #print axioms line must be answered by
# "does not depend on any axioms" or a list whose every member is propext, Classical.choice or Quot.sound
# (any subset, any order). sorryAx or any other axiom, a missing answer or an error all fail.
nexp=$(grep -c '^#print axioms' axioms_all.lean)
nstd=$(awk '/^.[^ ]+. does not depend on any axioms$/ {n++; next}
  /^.[^ ]+. depends on axioms: \[[^]]*\]$/ {l=$0; sub(/^[^[]*\[/,"",l); sub(/\]$/,"",l); m=split(l,a,", "); ok=(m>0);
    for(i=1;i<=m;i++) if(a[i]!="propext" && a[i]!="Classical.choice" && a[i]!="Quot.sound") ok=0; if(ok) n++}
  END {print n+0}' axioms_all.out)
echo "$nstd of $nexp theorems use only standard axioms (lean exit $lrc)"
[ "$lrc" -eq 0 ] && [ "$nstd" -eq "$nexp" ] && ! grep -q "error" axioms_all.out || status=1
echo "=== done $(date -u +%FT%TZ), exit $status"; exit $status

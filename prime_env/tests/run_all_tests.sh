#!/usr/bin/env bash
# Run every grader test, one after another, and keep each exact output in tests/logs/.
# Usage: run_all_tests.sh   (needs elan with the pinned toolchain; PY=... picks the Python, default python3)
set -u
S="$(cd "$(dirname "$0")/.." && pwd)"
PY=${PY:-python3}
T=$S/lean_mod_add_proof/lean_mod_add_proof/tasks
mkdir -p logs work
cd $S/tests
export OMP_NUM_THREADS=1
run() { # name task reply extra...
  name=$1; task=$2; reply=$3; shift 3
  echo "=== $name  (task $(basename $task), reply $(basename $reply) $*)"
  t0=$(date +%s.%N)
  $PY run_grade.py $task $reply "$@" > logs/$name.txt 2>&1
  t1=$(date +%s.%N)
  printf 'wall %.1fs\n' $(echo "$t1 - $t0" | bc) >> logs/$name.txt
  grep -E '"reward"|"stage"|"reason"|^wall ' logs/$name.txt | sed 's/^/    /'
}
run i_bruteforce_p7            $T/p7_h8_s0  subs/i_bruteforce_p7.md
run ii_sorry_p7                $T/p7_h8_s0  subs/ii_sorry_p7.md
run ii_b_sorry_noguard_p7      $T/p7_h8_s0  subs/ii_sorry_p7.md --no-guard
run iii_native_decide_p7       $T/p7_h8_s0  subs/iii_native_decide_p7.md
run iii_b_native_noguard_p7    $T/p7_h8_s0  subs/iii_native_decide_p7.md --no-guard
run iii_c_decide_native_noguard_p7 $T/p7_h8_s0 subs/iii_b_decide_plus_native_p7.md --no-guard
run iv_skipKernelTC_guard_p7   wrong_task/p7_h8_s0_WRONG subs/iv_skipKernelTC_false_p7.md
run iv_b_skipKernelTC_noguard_p7 wrong_task/p7_h8_s0_WRONG subs/iv_skipKernelTC_false_p7.md --no-guard --keep
run v_wrong_statement_p7       $T/p7_h8_s0  subs/v_wrong_statement_p7.md
run v_b_renamed_p7             $T/p7_h8_s0  subs/v_b_renamed_p7.md
run vi_wrong_network_p7        wrong_task/p7_h8_s0_WRONG subs/i_bruteforce_p7.md
echo "=== done"

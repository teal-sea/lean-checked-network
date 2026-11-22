# Adversarial re-verification of the lexnet proof package

Branch: `muse/lexnet-ci`, based on `73e5ab9` (PR #24 lexnet-proof content:
`7ac2937` plus `73e5ab9`), itself based on `0214aa3` (main at branch point).
Date of runs: 2026-11-22. Host: 4 vCPU, 3.8 GiB RAM total, no swap, shared
host (other tenants used about 1.8 to 2.0 GiB during the runs, leaving about
2.0 GiB available). All Lean work used the pinned toolchain
`leanprover/lean4:v4.35.0-rc2`, installed during this session with elan
because only v4.35.0 and v4.36.0 were present at the start.

Status note, closed after the run finished: the unmodified official
`./verify.sh` completed. Stdout is `/tmp/lex-verify-official.log` and ends
`VERIFY PASS`. leanchecker exit 0, wall 4752s. The capped-parallelism replay
in section 3 is a separate earlier run, also exit 0. Nothing below claims a
check that was not run.

## 1. Harness tests and regeneration check

Command:

```sh
cd lexnet && python3 -B -m unittest discover -s tests -v
```

Real output summary (full log kept in the session, decisive lines pasted):

```text
test_check_passes_on_package (test_harness.Generators.test_check_passes_on_package) ... upstream/SHA256SUMS: OK
SHA256SUMS.lean: OK
gen_lean.py -> lean/Pilot.lean: deterministic=True byte-identical-to-committed=True
gen_extra.py -> lean/NetExtra.lean: deterministic=True byte-identical-to-committed=True
gen_float.py -> lean/FloatTables.lean: deterministic=True byte-identical-to-committed=True
generate --check: PASS
ok
----------------------------------------------------------------------
Ran 36 tests in 12.274s

OK
```

Command:

```sh
cd lexnet && python3 -B generate.py --check
bash -n verify.sh && bash -n controls.sh
sha256sum -c upstream/SHA256SUMS
sha256sum -c SHA256SUMS.lean
```

Real output:

```text
upstream/SHA256SUMS: OK
SHA256SUMS.lean: OK
gen_lean.py -> lean/Pilot.lean: deterministic=True byte-identical-to-committed=True
gen_extra.py -> lean/NetExtra.lean: deterministic=True byte-identical-to-committed=True
gen_float.py -> lean/FloatTables.lean: deterministic=True byte-identical-to-committed=True
generate --check: PASS
verify.sh syntax OK
controls.sh syntax OK
upstream/lexnet/lexnet.c: OK
upstream/lexnet/lexnet_kernel.h: OK
upstream/lexnet/lexnet_weights.bin: OK
upstream/lexnet/README.md: OK
(28 lines of "OK" for SHA256SUMS.lean, one per Lean source)
0188bedb0765ed5fee5a8763ca09f6dd25faf2eeac5dc775bb06ef306d7cebe2  upstream/lexnet/lexnet_weights.bin
```

The weight file is 80136 bytes and starts with the magic `LEXNET01`. Its
SHA-256 matches `upstream/SHA256SUMS`, the README provenance line, and the
generated header comment in `lean/Pilot.lean` line 3.

## 2. Toolchain

At session start `elan toolchain list` showed only v4.35.0 and v4.36.0, so
the pinned v4.35.0-rc2 was installed:

```text
info: downloading https://releases.lean-lang.org/lean4/v4.35.0-rc2/lean-4.35.0-rc2-linux.tar.zst
info: installing /opt/data/.elan/toolchains/leanprover--lean4---v4.35.0-rc2
leanprover/lean4:v4.35.0-rc2 installed - (timeout reading lean version)
Lean (version 4.35.0-rc2, x86_64-unknown-linux-gnu, commit 11acb17ec6b07a8f9e9173e6845197929540936b, Release)
```

All Lean commands below put that toolchain bin directory first on PATH, as
`verify.sh` requires (it checks the `lean --version` string for equality
with `lean-toolchain` and derives `leanchecker` from `lean --print-prefix`).

Operator error recorded for honesty: `leanchecker --version` was run once
while probing. It does not print a version and exit; it treats the argument
as work, held about 1.6 GiB RSS, and was terminated. No evidence below comes
from that invocation.

## 3. Full build, axiom audit and replay with capped parallelism

To size the job for 2.0 GiB available, the 17 theorem-closure modules plus
`Axioms.lean` were first built one at a time exactly as `verify.sh` does
(fresh private directory, copied sources, `LEAN_PATH` set to the work root,
`lean -o lean/M.olean lean/M.lean`), except with `-j2` and
`LEAN_NUM_THREADS=2` instead of the shipped `-j4`, under
`nice -n 10 ionice -c 2 -n 7`. Peak RSS is the child `ru_maxrss` high water
mark, so later small modules repeat the running maximum.

Real output:

```text
Reference exit=0 wall=5.4s child_maxrss=507716KiB (0.48GiB)
Units exit=0 wall=1.4s child_maxrss=526536KiB (0.50GiB)
Pilot exit=0 wall=33.8s child_maxrss=1490812KiB (1.42GiB)
NetExtra exit=0 wall=12.7s child_maxrss=887952KiB (0.85GiB)
Hash exit=0 wall=1.6s
Flags exit=0 wall=4.9s
Fwd0 exit=0 wall=0.7s
Fwd1a exit=0 wall=70.0s child_maxrss=1474892KiB (1.41GiB)
Fwd1b exit=0 wall=73.3s child_maxrss=1474236KiB (1.41GiB)
Fwd1c exit=0 wall=73.2s
Fwd1d exit=0 wall=51.9s
Fwd1 exit=0 wall=0.9s child_maxrss=773012KiB (0.74GiB)
Fwd2 exit=0 wall=2.7s child_maxrss=862420KiB (0.82GiB)
Fwd3a exit=0 wall=1.5s
Bwd exit=0 wall=6.0s child_maxrss=1153872KiB (1.10GiB)
Fwd3 exit=0 wall=1.6s
Full exit=0 wall=0.6s
Axioms exit=0 wall=0.5s
```

Build logs contain no `sorry` and no `error` lines (checked with grep over
all 18 logs). The only diagnostics are linter and deprecation warnings in
Bwd, Hash, NetExtra and Fwd3a, identical to the worker receipt logs.

Axiom audit. `Axioms.log` in full:

```text
'lexnet_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lexnet.num_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lexnet.fwd_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lexnet.fwd_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lexnet.bwd_all' depends on axioms: [propext]
'Lexnet.backward_ok' depends on axioms: [propext]
'Lexnet.kw_flag' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lexnet.ty_flag' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lexnet.co_flag' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lexnet.kw_char' depends on axioms: [propext, Classical.choice, Quot.sound]
'Hash.wordHash_inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lexnet.core_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lexnet.hash_first' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lexnet.hash_second' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lexnet.hash_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lexnet.hash_idle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lexnet.automaton_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Checker output: `axiom allowlist OK: 17 records, exact inventory;
lexnet_correct uses exactly ['Classical.choice', 'Quot.sound', 'propext']`,
exit 0. The log is byte-identical to
`verification/packaging/build/Axioms.log` (verified with diff).

Object identity: all 18 rebuilt `.olean` SHA-256 values match
`verification/nanoda/objects.sha256` exactly (18 of 18 MATCH, checked
programmatically). The nanoda receipt therefore covers objects reproduced
in this session from the committed sources. Nanoda itself was not rerun
(no nanoda binary in the worktree; the 27 MB export is not included).

Kernel replay on those objects, scrubbed environment as in `verify.sh`
lines 61 to 62 (`env -i`, toolchain PATH, private HOME and TMPDIR,
`LEAN_NUM_THREADS=2`), under nice and ionice:

```text
leanchecker --fresh lean.Full exit=0 wall=420.1s child_maxrss=1516240KiB (1.45GiB)
leanchecker.log bytes=0
```

The empty log matches the packaging receipt `leanchecker.log` (0 bytes).
Exit 0 is the evidence; leanchecker prints nothing on success here.

## 4. Unmodified `./verify.sh` (the run the PR said was never repeated)

Stdout kept at `/tmp/lex-verify-official.log`. Decisive lines:

```text
run directory: /tmp/lex-verify-parent/run.Pki3BG
== 1. pinned inputs, accepted sources, generators
generate --check: PASS
== 2. clean sequential build of the theorem closure
Reference exit=0 wall=1s
Units exit=0 wall=1s
Pilot exit=0 wall=27s
NetExtra exit=0 wall=12s
Hash exit=0 wall=2s
Flags exit=0 wall=4s
Fwd0 exit=0 wall=1s
Fwd1a exit=0 wall=69s
Fwd1b exit=0 wall=69s
Fwd1c exit=0 wall=68s
Fwd1d exit=0 wall=251s
Fwd1 exit=0 wall=18s
Fwd2 exit=0 wall=66s
Fwd3a exit=0 wall=28s
Bwd exit=0 wall=65s
Fwd3 exit=0 wall=23s
Full exit=0 wall=6s
Axioms exit=0 wall=5s
== 3. axiom inventory
axiom allowlist OK: 17 records, exact inventory; lexnet_correct uses exactly ['Classical.choice', 'Quot.sound', 'propext']
== 4. leanchecker --fresh lean.Full (Lean's kernel replay, scrubbed environment)
leanchecker exit=0 wall=4752s
logs kept in /tmp/lex-verify-parent/run.Pki3BG/logs
VERIFY PASS
```

`VERIFY PASS` is printed by `verify.sh` only after leanchecker returns 0.
`leanchecker.log` in that run directory is 0 bytes, matching the packaging
receipt. Fwd1d at 251s is the loaded-host outlier; the same module was 51.9s
in the earlier capped run.

## 5. Changed-weight control

`/tmp/lex-controls.log`, from `./controls.sh` in this session:

```text
run directory: /tmp/lex-controls-parent/run.Hbr6mW
head {'kind': 'head coefficient', 'where': 'head[8][5]', 'before': 9.0, 'after': 7.5, 'byte_offset': 79752}
mutant Reference exit=0
mutant Pilot exit=0
mutant Bwd exit=1
control OK: exactly one error at the frozen location, the false-proposition diagnostic, after two successful prerequisites
```

## 6. CI

`.github/workflows/lexnet.yml` runs the harness and `generate.py --check` on
pull requests that touch `lexnet/`, then the unmodified `./verify.sh` and
`./controls.sh`. `LEXNET_WORK` is a parent directory, which is what both
scripts require. Timeout is 180 minutes because this host needed about 91
minutes (build plus the 4752s replay) while loaded. Action pins match the
repo's other workflows (`checkout@v5`, `setup-python@v6`,
`upload-artifact@v4`).

YAML was not validated with a YAML library (PyYAML is not installed here).
Shell syntax of `verify.sh` and `controls.sh` was checked with `bash -n`.

## 7. Re-check after the worker was cut off

The Muse job died on a 429 before it could finish this report or commit.
Proof sources were not modified: `git status` showed only this report and
the new workflow. Re-run here, not taken from the worker's log:

```text
Ran 36 tests in 11.709s
OK
generate --check: PASS
bash -n verify.sh && bash -n controls.sh  -> syntax_ok
```

## 8. What was not done

No separate adversarial write-up of the proof text. The mechanical pins
were re-checked (upstream digests, generator byte-identity, axiom
allowlist, head-coefficient mutant rejected, accepted Lean sources
untouched). A line-by-line audit of the 28 proof sources was not repeated
in this salvage pass. Nanoda was not rerun; no nanoda binary in the tree.


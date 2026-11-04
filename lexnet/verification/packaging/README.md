Receipts from running the public commands in this repository layout, once, as packaging acceptance.
Producer exit codes are the ones printed in the logs (`verify.sh` and `controls.sh` run each compiler
directly and stop on the first non-zero exit).

- `verify.log`: `./verify.sh` output: digests and generator check PASS, 17 closure modules + `Axioms.lean` (18 compiler runs) compiled
  one at a time (exit 0 each; 712 s in total), axiom allowlist OK, `leanchecker --fresh lean.Full` exit 0 (1247 s; 712 + 1247 = 1959 s, about 33 minutes, on a
  shared, loaded host), `VERIFY PASS`.
- `build/*.log`: raw compiler output per module, warnings included (nothing filtered).
- `leanchecker.log`: raw replay output.
- `controls.log`, `controls-mutant-*.log`: `./controls.sh`: mutant Reference exit 0, mutant Pilot exit 0,
  mutant Bwd exit 1 with Lean's "Tactic `decide` proved that the proposition ... is false".
- `tests.log`: `python3 -m unittest discover -s tests`.
Absolute local paths were replaced by `<scratch>`, `<toolchain>` and `<home>`.

Historical note: this is the original capture, kept unedited. It was produced with the first version of the
harness (workdir reused, axiom and control checks that matched phrases loosely, `-I` generators without `-B`).
The checks and directory handling were repaired afterwards; see `../repair/README.md`. The unchanged proof
bytes and the positive build and replay logs here still stand.

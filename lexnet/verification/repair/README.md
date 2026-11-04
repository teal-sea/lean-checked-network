Repair of packaging issues found by an independent review. The Lean proof bytes, generators `gen_*.py`,
`upstream/` and `SHA256SUMS.lean` are unchanged. The main build and replay were not rerun: the compile
commands are unchanged, and the original positive logs in `../packaging/` still stand.

Real evidence (real Lean 4.35.0-rc2):
- `controls.log`, `controls-mutant-*.log`: `./controls.sh` under the repaired layout (new private
  `run.XXXXXX` child of `LEXNET_WORK`): mutant Reference exit 0, mutant Pilot exit 0, mutant Bwd exit 1,
  accepted by the stricter `check_control.py` (exactly one error, at `lean/Bwd.lean:57:6`).
- `generate-check.log`: `python3 -B generate.py --check`, PASS, with `-I -B` generator subprocesses.
- `shell-syntax.log`: `bash -n` on both scripts.

Synthetic harness evidence (not proof evidence):
- `tests.log`: 36 tests, all OK. Axiom tests (10, one of them a CLI exit-code test) mutate the real captured `Axioms.log`:
  only the main line, a missing helper, duplicate plus error plus garbage lines, an unexpected name, a main
  theorem with an extra axiom, a `sorry` warning, an extra axiom in a helper, a weaker main theorem. Control
  tests (12) mutate the real captured Bwd log: added error, error in another file, phrase-only spoof, wrong
  line, wrong file, other error text, missing or extra prerequisite exits, failed prerequisite, wrong
  target exit, leading garbage. The 11 workdir tests run `verify.sh` against a copy of the package with
  **stub** `lean` and `leanchecker` scripts (labelled in the test source): package directory, its
  subdirectory and a symlink to it as `LEXNET_WORK` are refused with exit 2 and the copy's tree hash is
  unchanged; a relative parent with pre-existing `lean/Reference.lean` and a sentinel file keeps both and
  gets one `run.*` child; two runs make two children; a module failure, a replay failure and a bad axiom log
  fail without touching sources; missing `lean` gives an actionable message and creates no directory; no
  `__pycache__` appears in the package.

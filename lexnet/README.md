# Lexnet: a neural syntax highlighter equals a short Lean program, on every input

[lexnet](https://huggingface.co/alpindale/lexnet) (Alpin Dale, Apache-2.0) is a bidirectional recurrent
network of about 984 non-zero weights that gives every byte of a C file one of eleven highlighting
classes. This folder holds a Lean 4 proof that, for every finite list of bytes, the network's exact
integer semantics assigns the same classes as a readable Lean reference program.

```lean
theorem lexnet_correct (bs : List Byte) : exactClasses bs = Ref.referenceClasses bs
```

`Byte` is `Fin 256`. `exactClasses` (in `lean/Pilot.lean`, generated from the pinned weight file by
`gen_lean.py`) runs the whole forward cell left to right, then the backward cell and the doubled argmax
head right to left, in exact `Int` arithmetic with earliest-index tie breaking. `Ref.referenceClasses`
is `lean/Reference.lean`: an 187-line file with no import and no weight,
network unit or generated table in it. Lean's kernel accepts the theorem with only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## What this does not say

- It is the network's **exact-arithmetic** semantics, not the float64 program. The optional files
  `lean/Cell.lean` to `lean/FloatCert.lean` kernel-check that every product and ordered partial sum of
  the forward cell is at most 2^53 in magnitude on reachable states. That is a statement about integer
  magnitudes only. It is not an IEEE-754 model and not a proof about the C code.
- Nothing here verifies the C loader, the C compiler, the Python weight parser used by the generators
  (`exact.py`), or the shipped `lexnet.c`. A separate run found the Lean reference and the shipped binary
  agree on the 12,350 bytes of `lexnet.c` (`verification/coordinator/`); that is a test, not a proof.
- It is equality with this particular highlighting **policy**, not ISO C lexing. The reference makes the
  policy's quirks visible. For example only the first 14 bytes of a word are remembered, so
  `_Static_assertSuffix` (a longer name that starts with the 14-byte keyword `_Static_assert`) is
  highlighted entirely as a keyword; an escaped newline does not continue a string or a `//` comment;
  bytes 128 to 255 are punctuation. See `verification/worker-logs/quirks.json` for checked examples.
- No claim of scientific priority is made.

## Layout

| Path | Role |
| --- | --- |
| `lean/Reference.lean` | The readable reference lexer (port of `spec.py`). The headline. |
| `lean/Pilot.lean` (+ `lean/Proof.inc`) | Generated exact semantics of the weights, plus the earlier automaton proof. `Proof.inc` is the hand-written proof text the generator appends. |
| `lean/NetExtra.lean` | Generated slices of the forward cell, tied to the full cell by `rfl`, and the keyword/type/constant threshold tables |
| `lean/Units.lean`, `lean/Hash.lean`, `lean/Flags.lean` | Threshold-unit lemmas; base-64 word hashes and their injectivity; keyword, type and constant flags equal list membership |
| `lean/Fwd0.lean`, `Fwd1a` to `Fwd1d`, `Fwd1.lean` | Kernel check of the 33 reachable automaton states against the reference, split into four files for memory |
| `lean/Fwd2.lean`, `Fwd3a.lean`, `Fwd3.lean` | Counter and hash-register arithmetic, the word-buffer invariant, the one-step forward theorem |
| `lean/Bwd.lean` | Backward cell and head equal one right-to-left step of the reference |
| `lean/Full.lean` | `lexnet_correct` |
| `lean/Axioms.lean` | Prints the axioms of the main theorems (checked by `verify.sh`) |
| `lean/RefCases.lean`, `Samples.lean` | Reference against 307 Python-spec cases; end-to-end examples. Not in the theorem closure |
| `lean/ExpectedFail.lean` | Earlier automaton-level control. It is meant to fail to compile |
| `lean/Cell.lean`, `FloatTables.lean`, `FloatBridge.lean`, `FloatBox.lean`, `FloatCert.lean`, `FloatAxioms.lean` | Optional range certificate (see above). Not in the default verification |
| `exact.py`, `gen_lean.py`, `gen_extra.py`, `gen_float.py`, `evidence/automaton.json` | Generators and their inputs. `evidence/automaton.json` is the reachable-automaton certificate `gen_lean.py` embeds. `spec.py` is the Python reference |
| `generate.py` | Single entrypoint: `--check` verifies digests and byte-identical, deterministic regeneration; no flag regenerates in place |
| `verify.sh`, `controls.sh`, `check_axioms.py`, `check_control.py`, `tests/` | Verification harness and its tests |
| `upstream/` | Pinned lexnet files (weights, C source, README), license and `SHA256SUMS` |
| `SHA256SUMS.lean` | Digests of every Lean source as accepted. Module names and bytes are unchanged from the accepted proof |
| `verification/` | Public receipts (see below). `FULL-REPORT.md` is the original proof report |

## Provenance

- Network: [`alpindale/lexnet`, revision `c59fe649f8143e81adaff70c32d82da4ca0b6ff3`](https://huggingface.co/alpindale/lexnet/tree/c59fe649f8143e81adaff70c32d82da4ca0b6ff3)
  (Alpin Dale, Apache-2.0), files pinned by `upstream/SHA256SUMS`. Weight file SHA-256
  `0188bedb0765ed5fee5a8763ca09f6dd25faf2eeac5dc775bb06ef306d7cebe2`. The upstream README says the weights
  were generated by Claude Fable 5.1.
- Credit: the feasibility work (exact evaluator, reference policy, automaton pilot, plan) was done by Codex.
  Claude Sonnet 5.5 completed the all-input proof, the Lean reference and the remaining generators. Both are AI agents.
- The Lean sources are copied byte for byte from the accepted proof package; `SHA256SUMS.lean` pins them.
  That package was a private working folder, so its revision is not given as a source. Toolchain
  `leanprover/lean4:v4.35.0-rc2`, Std only, no Mathlib.
- Trust boundaries: the Lean toolchain, the operating system, Python and the weight parser `exact.py` are
  trusted and not verified here. The `SHA256SUMS` files detect drift or accidental edits; they are not
  signatures and do not show where a file came from. Whether the pinned weights are the published ones
  rests on the revision above.
- The proof was independently rebuilt and checked, see the receipts below.

## Reproduce

Needs bash, Python 3 (stdlib only) and the pinned Lean toolchain (`lean`, `leanchecker`). The one packaging
run measured 1959 seconds, about 33 minutes (712 s of compilation plus 1247 s of `leanchecker` replay), on a
loaded shared host. Runtime depends on the machine and other load. The main-chain compile measurements were
under 2 GiB per Lean process, with at most 4 Lean threads and one compiler at a time.

```sh
cd lexnet
python3 -B -m unittest discover -s tests   # 36 harness tests, about 13 s (stubs for lean; not proof evidence)
python3 -B generate.py --check             # input digests, source digests, deterministic regeneration
./verify.sh                             # the full check; fails closed
./controls.sh                           # separate: changed-weight negative control, about a minute
```

`verify.sh` checks digests and generator equality, compiles the 17 modules of the theorem closure plus
`Axioms.lean` (18 compiler runs) one at a time in a new private directory (explicit `LEAN_PATH`, nothing
prebuilt), requires the log of `Axioms.lean` to be exactly the 17 expected axiom records with no other
line, `lexnet_correct` using exactly the three standard axioms and every other theorem a subset, and runs `leanchecker --fresh lean.Full` in a
scrubbed environment. `LEXNET_WORK` names a parent directory (created if missing, never wiped or reused): each run creates a
fresh `run.XXXXXX` inside it, and a parent that is or lies inside this package directory is refused. The
generators run with `python -I -B`, avoiding bytecode writes under the source tree. `leanchecker` is Lean's own
kernel replay of the compiled objects: it uses the same kernel that accepted the proof, so it guards
against stale or tampered objects, not against a kernel bug.

`controls.sh` changes one head weight (`head[8][5]`, 9.0 to 7.5), regenerates `Pilot.lean` with the same
generator and compiles the unchanged `Reference.lean` and `Bwd.lean`. It passes only if the first two
compile and `Bwd.lean` exits 1 with Lean's `decide` reporting a false proposition. Minimal witness: the
three bytes `#//` get classes `988` from the original weights and `999` from the mutant.

## Verification receipts (`verification/`)

All raw logs were copied as produced, with the redactions listed below.

- `coordinator/`: an independent rebuild of the 17 closure modules plus `Axioms.lean` from a fresh clone, byte-identical
  regeneration of `Pilot.lean` and `NetExtra.lean`, the axiom audit, `leanchecker --fresh lean.Full`
  (exit 0, 773 s), the head mutant rejected with a false-proposition error, and the Lean reference
  equal to the shipped binary on `lexnet.c`. `VERDICT.md` states two early harness errors (a compile
  outside the Lean root; a deprecation warning written into a compared file) and their corrections; the
  first failed attempts are not evidence.
- `nanoda/`: a second, separately implemented kernel checker (nanoda) run on an export of
  `lexnet_correct` from the coordinator's rebuilt objects. It reported "Checked 4595 declarations with no
  typechecker errors". It also printed one pretty-printer error, "Unable to print axioms", so the claim is
  exactly "no typechecker errors", not "no errors". The axiom allowlist (`propext`, `Classical.choice`,
  `Quot.sound`) was enforced with unpermitted axioms a hard error. The receipt covers only the recorded
  objects: `objects.sha256` lists the compiled `.olean` hashes and `export.sha256` the export hash. The
  27 MB export itself is not included.
- `worker-logs/`: the proof author's per-module build logs, replay logs, axiom log, both mutant
  rejections and their witnesses, the 307-case reference test summary and the quirk examples.
- `packaging/`: the run of `verify.sh` and `controls.sh` in this repository layout, kept as originally captured (see `packaging/README.md`), and `repair/`: later harness repairs, with real controls rerun and clearly labelled synthetic stub tests.
- `final/`: the coordinator's independent acceptance of those repairs, including all 36 tests, real changed-weight control, real source-directory refusal, malformed-log rejection and byte-for-byte source preservation.

Redactions: absolute local paths in the copied logs were replaced by `<scratch>`, `<toolchain>`,
`<home>` or `<package>`. Machine-specific launcher scripts (the coordinator's `verify.sh` and nanoda's `nanoda.sh`) were
left out; their commands are `leanexport lean.Full -- lexnet_correct`, then `nanoda_bin` with the config
`nanoda/nanoda.json`. Nothing else was altered.

# Adversarial audit, 2026-10-25

Three reviewing agents were each told to break one part of the work: the Lean statements
(including transformer, phasegrid, sweep, rnn and ACAS), the Lean trust base (scripts, CI,
release gates), and the claims and numbers across the write-ups. They are AI agents of the
same kind that wrote the project, working from the repository alone, so they can share the
author's blind spots; this is not outside review. A fourth pass recomputed the MLP numerics
and re-read the scripts against the committed logs.

The 2026-10-15 audit of the trained MLP and circle-only theorems is kept below; this entry
covers the repository as it stood after the transformer r2 and ACAS evidence releases.

## What could not be broken

- **MLP theorems still match the networks.** `verify_weights.py` and an independent
  recomputation: Trained and CircleOnly Lean tables equal `network/*.npz`; 0 wrong of
  12,769; Fault wrong on 226; FixedPhase12/16, Mod12All and Mod257Min all 0 wrong. Min margins
  32,654,491 at (13, 53) and 1,980,696 at (10, 25). Residual (trained − circle-only): 50 right.
  114 live neurons; median energy share 0.971; third harmonic largest leftover in 114/114.
  Joint circle certificate: all 12,769 pairs; tightest ratio 0.017. Production Lean under
  `lean/` has no `sorry`, custom `axiom`, `opaque`, `extern`, `implemented_by`, `unsafe` or
  `skipKernelTC`.
- **Transformer statement content.** `TransformerBridge.FinalRaw.raw_model_adds_mod_113`
  quantifies all `Fin 113` pairs, uses `S = 256`, exact real softmax, strict logit max and
  first argmax, with no hypotheses. Standard axioms only in the documented audit. The object
  is the quantised model, not the float checkpoint.
- **RNN every-length claim.** `RnnAdder.Trained.adds` takes an arbitrary `List Input`; the
  proof is reachability of five states plus induction. Unreachable states are out of scope as
  the README states.
- **Sweep wrong-pair lists (as data).** The six checkpoints' named wrong pairs in
  `sweep/tests/learning-curve/*/result.json` match the learning-curve write-up (3, 2, 3, 2, 2,
  0); all listed wrong pairs are held-out under seed 0, frac 0.5.
- **ACAS proposition shape.** `Frozen.ACASXu_1_1_Property1` is the closed box → `Y_0 < threshold`
  on TorchLean exact-real semantics for network 1_1; STATUS and README both state the IEEE /
  ONNX / aircraft limits.
- **phasegrid numeric instances.** FixedPhase12 and Mod257Min regenerate byte-equal to the
  committed npz from `make_fixed_phase6.py`; 0 wrong; margins 1,021,168 and 375,872.

## What was wrong, and what changed

| Finding | Change |
| --- | --- |
| README said the 128-neuron run “was kept (`runs/p113_h64.log`)”; that log is the 64-neuron run | Cite `runs/p113_h128.log` for the kept 128-neuron run |
| `lean_run.log` records “40 of 40” modules and two axiom lines (2026-10-15, Trained+CircleOnly). Today's `run_lean.sh` finds **85** modules (adds FixedPhase12/16 and Mod12All) and prints five axiom lines; Mod257Min remains only in `run_lean_fixed_phase.sh`, which is **not** in `check.yml`. `lean_run_fixed_phase.log` still describes FixedPhase40/448 and Mod7All builds that the current script no longer runs | README cites the log as historical for Trained+CircleOnly and states today's script/CI scope; demote the fixed-phase log as historical |
| VERIFY.md and older notes call r2 a “prerelease”; GitHub lists `transformer-final-raw-evidence-r2` as Latest with `isPrerelease: false` (published 2026-10-25 01:22 UTC / 2026-10-24 20:22 America/Bogota) | VERIFY.md and STATUS point at r2 as the release |
| `transformer/STATUS.md` top says `hT`/`hB`/`hA` proved, but the history closing line still says they “remain open”; recheck pointer still names the pre-r2 asset; `RECHECK.md` still documents an overlay required for the old bundle | Mark the open line as superseded; point STATUS at r2; mark RECHECK overlay as historical for the pre-r2 archive |
| README “In short” packed the every-modulus Mathlib theorem with the 12-neuron 8-bit nets. Those nets run at M=127, below the cycle theorem's sufficient scales (≈257 at p=113, ≈579 at p=257), so they rest on brute-force checks only (already stated later in the README) | Split the In-short bullet |
| Learning-curve Lean packages were generated in scratch and are **not** in the repo; only `result.json` remains. Kernel-checked circle-only at those checkpoints is the **rescaled** Fast-range version | README learning-curve row states both facts |
| Single-weight claim used `254 × 255²` as if it covered every table. That bound covers a W2-style edit; a uniform product bound for an E1/E2 edit can exceed the margin (measured `max\|E1+E2\| = 249`). Empirical search still did not flip answers | Restate as a W2-style derived bound plus measured E-table search |
| “~20 min on one core” for `train.py` failed on this audit host (~3 h wall with numpy); integer `*q` weights still reproduced | Soften to machine-dependent; keep the integer-reproducibility claim |
| “Two kernels checked it” / nanoda counts mix three scopes (MLP audit nanoda 0.4.17 / 2,569; transformer 0.4.19 / 82,927; ACAS 59,489), each with one axiom pretty-printer error; default transformer verify replays 20 new modules and does not invoke nanoda; release-gate **passes** when `--from-source` reports a recorded byte mismatch | Label nanoda scopes; note pretty-printer error and default leanchecker scope; keep the honest VERIFY TCB wording |
| Default VERIFY omits `--controls`; “11 tampering attacks” live in release-note history, not an in-repo enumerated suite. Branch protection requiring `verify-release` is an admin setting, not encoded in the repo | Soften the attack-count claim; note branch protection is out of band |
| `run_lean_fixed_phase.sh` hardcodes `PATH="/root/.elan/bin"` | Use `$HOME/.elan/bin` like `run_lean.sh` |

## Trust boundary (unchanged facts, now explicit)

- Transformer default reader: authenticated publisher → checksums → shipped oleans as artifacts →
  proposition/axiom checks → `leanchecker` on the documented new modules. It does **not**
  establish whole-bundle source reproduction; the from-source probe of `TransformerCore.Model`
  still differs in bytes (`VERIFY.md`).
- Checksums assume authenticity of VERIFY.md or the release notes; they do not establish
  publisher identity.
- MLP CI (`check.yml`) runs `run_lean.sh`, not `run_lean_fixed_phase.sh` and not ACAS.
- Lean binaries: MLP path has no independent official-digest pin; release paths pin publisher
  inventories. `elan-init.sh` is still fetched from `leanprover/elan/master`.

## Not checked

- Full Lean rebuilds / nanoda replays of transformer, ACAS, phasegrid Mathlib, or Mod257Min.
- Exhaustive recompute of the 1,442,897-triple decomposition ratio 0.347 (300-sample worst here
  0.119; not a falsification).
- Exhaustive single-weight attack over every weight and pair.
- Live download and end-to-end `verify.sh` of the r2 asset in this session.
- The eleven historical tampering attacks against the release verifier.
- Official Lean toolchain binary comparison (still open from 2026-10-15).

---

# Adversarial audit, 2026-10-15

Three reviewing agents were each told to break one part of the work: the Lean statement, the
Lean trust base, and the claims and numbers in the write-up. They are AI agents of the same kind
that wrote the project, working from the repository alone, so they can share the author's blind
spots; this is not outside review. Their scripts and logs were kept in the session's scratch space,
not in this repository.

## What could not be broken

- **The Lean theorems are about these networks.** An independent parser matched all
  3 × 113 × 128 entries of each `Weights.lean` to `network/*.npz` (orientation and the
  `.negSucc` sign encoding included). A Lean program read the weights back out of the checked
  build and found them identical. The network definition (`nth`, `hidden`, `dot`, `scores`,
  `argmax` with first-index ties) matches the description, and both theorem statements cover
  every `a, b < 113` with their own namespace's `answer`.
- **Every answer, recomputed outside Lean.** Pure Python mirroring the Lean definitions: trained
  network 0 wrong (smallest margin 32,654,491 at (13, 53)), circle-only network 0 wrong
  (1,980,696 at (10, 25)), fault network 226 wrong, no ties.
- **Training reproduces.** A full rerun of `train.py` gives the same integer weights exactly;
  `train_idx` is 6,384 distinct pairs.
- **Clean rebuild and axioms.** A rebuild from source with no cache completed (43 jobs, no
  warnings, no `sorry`); `#print axioms` gives `propext, Classical.choice, Quot.sound` for both
  main theorems and for `answer_eq_fastAnswer`. A scan of all 857 constants found no axiom,
  `opaque`, `extern` or `implemented_by`.
- **Independent checkers.** `leanchecker` (shipped with the toolchain) replayed all 40 modules:
  40 OK. (`run_lean.sh` at that date replayed the same 40; the root file only imported them.)
  **nanoda 0.4.17, a separate type checker written in Rust, checked the three main
  theorems: 2,569 declarations, no errors**, standard axioms only. lean4lean could not read this
  toolchain's files; con-ron did not finish in 75 minutes.
- **The fast evaluator's checks bite.** Weakening any of them (the digit bound, the range
  check, the length check, the sign check, a shift of 127 instead of 128, dropping a digit)
  breaks the proof of `answer_eq_fastAnswer`. A planted single-entry fault
  (`E1[106][70]` from 88 to 429, one pair wrong) was rejected by the kernel at exactly row 106.
- **The circle certificate is sound on every case.** Its bound never exceeds the true gap on any
  of the 12,769 pairs, and the decomposition error stays within its bound on all 1,442,897
  triples (worst ratio 0.347).
- **Measured numbers.** 114 live neurons; median 97% of weight energy in one frequency; third
  harmonic largest leftover in 114 of 114; 50 pairs right with the circle waves removed; the
  single-weight bound holds (worst single changes found leave margins near 19 to 20 million).

## What was wrong, and what changed

| Finding | Change |
| --- | --- |
| False: "the 64-neuron run got 2 or 3 pairs wrong at every checkpoint"; it was right on all pairs at step 12,000 | README corrected |
| The circle certificate's 82% came from taking each table's worst case separately; taking the worst case over the wrong answers jointly certifies **all 12,769 pairs** with the same bounds | `mechanism.py` now reports both; README and MECHANISM.md updated |
| Cost overstated: "a ninth of the multiplications" compared 2^200-sized products with 64-bit ones, and "about p²·H (21 million)" was not p²·H | Restated: the certificate is not faster (6 s against 0.3 s in numpy); its value is that it is built from the explanation |
| "About 20 CPU-hours" for the direct Lean route was an extrapolation, not a measurement | Restated as 7 to 20 CPU-hours, extrapolated from one row in two encodings |
| `run_lean.sh` trusted `lake build` and `#print axioms`, which a `set_option debug.skipKernelTC true` can fool (shown with a planted `2 + 2 = 5`) | The script now replays every module with `leanchecker`, which rejects that trick, and exits non-zero on any failure. The package sets no such option |
| Figure caption "always turns by the same angle" | Now "on average"; steps range from 0.56 to 1.42 of 11/113 of a turn |
| The circle-only weights reach 130, outside the [-127, 127] stated for the frozen weights | Stated |
| Missing prior work: Wu, Jaburi, Drori, Gross (2024; ICLR 2025) | Added |
| TorchLean's results described too narrowly | Restated |
| Smaller: training time (about 20 minutes, not an hour), `mechanism.py` default harmonics, "below chance" wording, the single-weight claim covering only the trained network | Fixed |

## Not checked

- The Lean toolchain binary was not compared with the official release.
- The planted-fault file tests one row (row 0, 2 of the 226 wrong pairs); the audit's own fault
  covered row 106.
- The circle certificate is exact arithmetic in Python, not in Lean.

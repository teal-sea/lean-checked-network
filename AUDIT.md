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
  40 OK. (`run_lean.sh` replays the same 40; the root file only imports them.) **nanoda 0.4.17, a separate type checker written in Rust, checked the three main
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

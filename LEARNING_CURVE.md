# A learning curve whose every point is a theorem

The 64-neuron run in `runs/p113_h64.log` is the one that was not right everywhere at every
checkpoint: frozen to whole numbers it got 3, 2, 3, 2, 2 pairs wrong at steps 2,000 to 10,000
and all 12,769 right at step 12,000. Retrained here with `train.py 113 64 0 1e-2 1.0 0.5 12000`
(2026-10-16), the run reproduced that log line for line, wrong counts and smallest margins
included. Each checkpoint is then a network, and each network's exact score is a theorem:

| Step | Held-out accuracy (float, measured) | Right pairs, frozen (numpy) | Theorem | Kernel verdict |
|---|---|---|---|---|
| 2,000 | 0.9995 | 12,766 of 12,769 | `H64Step2000.right_on_12766` | **kernel-checked**, 382 s on 4 cores, standard axioms |
| 4,000 | 0.9997 | 12,767 | `H64Step4000.right_on_12767` | **kernel-checked**, 381 s on 4 cores, standard axioms |
| 6,000 | 0.9995 | 12,766 | `H64Step6000.right_on_12766` | **kernel-checked**, 381 s on 4 cores, standard axioms |
| 8,000 | 0.9997 | 12,767 | `H64Step8000.right_on_12767` | **kernel-checked**, 376 s on 4 cores, standard axioms |
| 10,000 | 0.9997 | 12,767 | `H64Step10000.right_on_12767` | **kernel-checked**, 372 s on 4 cores, standard axioms |
| 12,000 | 0.9998 | 12,769 | `H64Step12000.right_on_12769` | **kernel-checked**, 377 s on 4 cores, standard axioms |

Training accuracy is 1.0000 at every checkpoint, so every wrong pair is a held-out pair: the
frozen network memorised the 6,384 training pairs by step 2,000 and generalised to the last three
held-out pairs between steps 10,000 and 12,000. That is grokking (Power et al., 2022) at the scale
of three pairs, and with the kernel's verdict on each point it is a fact about these six networks
rather than a plot.

**How.** `make_curve.py` copies each checkpoint into `network/`, writes its weights and table with
`gen_lean.py … norows` (no row proofs: the network is not right on every pair), and its count
theorems with `gen_count.py`: for each row `a`, one kernel evaluation decides that the fast
evaluator's checks pass on the row and how many `b` get `(a + b) % 113` right; `Count.lean` sums
the 113 rows through `rowCount_eq_fastRowCount` (`lean/LeanCheckedNetwork/Count.lean`) into
`right_on_N`, a statement about `count`, the plain definition over `answer` in `Network.lean`. The
six `Count` modules are imported by the root, so `run_lean.sh` and the Actions workflow build and
replay them with everything else. That is where the CI time went: the `lean` job of
`.github/workflows/check.yml` took 1 h 41 min on GitHub's runner for the merge of PR #4 (run
38904544116, 2026-10-16 13:00:16Z to 14:41:06Z, of which `run_lean.sh` 1 h 39 min) against 30 min on
the push before it (run 38891458216, 11:05:17Z to 11:35:09Z), because the root now also imports the
six count modules (2,269 s of build on 4 cores here, the table above, before their replay), the 12-,
16- and 40-neuron fixed-phase networks (522 s, `FIXED_PHASE.md`) and moduli 7 and 12 (10 s). The
448-neuron and modulus 257 networks are not in the root and stay in `run_lean_fixed_phase.sh`.

**What this is not.** Six points of one run at one width. The ablations, the circle-only
reduction and the margins per checkpoint are the same machinery and are not run here. A study
across data fraction, weight decay, width and seed is the proposal in the vault, not this file.
These six modules are also the subject of an open item: `sweep/WrongSet.lean` states a wrong
network's score as an explicit list of pairs, which implies the count, and the plan in
`FIXED_PHASE.md` and `sweep/README.md` is to regenerate the six through the sweep route, with a
`right_on_count` corollary, when they are next touched (about 40 minutes of kernel time).

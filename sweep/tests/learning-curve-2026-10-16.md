# A learning curve whose every point is a theorem: the 64-neuron run, 2026-10-16

The run in `runs/p113_h64.log` is the one that was not right everywhere at every checkpoint. Each
checkpoint below was produced by `run_one.py 113 64 0 0.5 1.0 STEP` (the repository's `train.py`,
seed 0, half the pairs, weight decay 1.0, learning rate 0.01, full batch, stopped at STEP), which is
the same deterministic trajectory as the logged run, so the frozen network at each step is the
logged checkpoint. The runner then froze it, built its circle-only reduction, generated a Lean package,
ran `lake build`, replayed every module with `leanchecker` (two at a time) and printed the axioms.
Namespace `LeanCheckedNetwork.Sweep.ST{STEP}`. 4-core container, the machine shared with one other run for most of the time.

The theorem for each network is `answer_iff_not_wrong`: for every pair `(a, b)`, the network answers
`(a + b) % 113` **if and only if** `(a, b)` is not in an explicit list, with the list proved to have
the stated length, to be strictly increasing (no pair listed twice) and to hold only pairs below 113,
so the count is exactly the number of wrong inputs (`sweep/WrongSet.lean`). An empty list is
`adds_mod_113`.

| Step | Accuracy, float (train / held-out) | Wrong pairs, frozen (kernel) | Smallest winning margin, right pairs only | Circle-only reduction, wrong (kernel) | Kernel | `leanchecker` | Axioms | Build |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2,000 | 1.0000 / 0.9995 | 3: (26, 35), (87, 97), (105, 54) | 1,427,183 | 235 | built, `wrongPairs_length`, `_nodup`, `_in_range` | 41 of 41, 1307 s | standard | 1420 s |
| 4,000 | 1.0000 / 0.9997 | 2: (5, 25), (105, 54) | 2,162,978 | 291 | built, `wrongPairs_length`, `_nodup`, `_in_range` | 41 of 41, 1249 s | standard | 1254 s |
| 10,000 | 1.0000 / 0.9997 | 2: (5, 25), (9, 84) | 1,988,014 | 341 | built, `wrongPairs_length`, `_nodup`, `_in_range` | 41 of 41, 1248 s | standard | 1331 s |
| 12,000 | 1.0000 / 0.9998 | 0: none | 175,330 | 328 | built, `wrongPairs_length`, `_nodup`, `_in_range` | 41 of 41, 1326 s | standard | 1487 s |

The margin column is `run_one.py`'s: the smallest gap between the right answer's score and the best other
score, over the pairs the network gets right. `train.py`'s log takes the minimum over all pairs, wrong ones
included, so its numbers are lower wherever a pair is wrong (both agree at step 12,000: 175,330).

Training accuracy is 1.0000 at every checkpoint, so every wrong pair is a held-out pair: the frozen
network memorised the 6,384 training pairs by step 2,000 and generalised to the last held-out pairs
between steps 10,000 and 12,000. That is grokking (Power et al., 2022) at the scale of three pairs,
and with the kernel's verdict on each point it is a fact about these six networks rather than a plot.

**The circles alone do not carry this run.** The circle-only reduction (each neuron cut to its single
circle wave, as `circle_only.py` does for the 128-neuron network, where it is right on every pair) is
wrong on hundreds of pairs at every checkpoint here, including step 12,000 where the trained network
is right on all 12,769. So the 64-neuron network's correctness rests on more than one wave per neuron:
the measured leftovers (third harmonics and the rest) are load-bearing at this width. Both facts are
kernel-checked, with the wrong lists named.
Circle-only note from the runner: circle_only.py's tables have an entry outside the fast evaluator's range, so all three tables were multiplied by the factor before rounding; the kernel-checked circle-only network is this rescaled one, not the one circle_only.py wrote; circle_only.py's tables used as written

The Lean packages were generated in a scratch directory outside the repository and are not committed;
`result.json` of each run, with the named theorems, module-by-module replay times and axioms, is in
`sweep/tests/learning-curve/`.

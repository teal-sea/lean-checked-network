# Result 15: three independent checks (2026-11-02)

Three agents, each with its own lens, read FINDINGS section 15, RULES.md (eleventh batch) and the raw
`curve_filters.csv` files after the batch.

## Numbers

Recomputed with an independent script (not `summarize_batch11.py` or `filters.py`): all 52 table cells,
every count and range in the prose, the guess scores and the prior-art additions match the raw tables. Two
wording defects, both fixed: the "3 to 88 wrong at step 100" range mixed in the one H 1024 seed whose
random frequency was never exact (3 to 23 for the four that were, 88 for the fifth), and "these
memorizers" covered result 1's ten memorizers where Liu & Lu was read on six. Not checkable against raw
data: the ten fresh random draws, which were run locally and not saved (`independent_check.md`).

## Overclaiming

No arithmetic errors; the defects were of scope, all fixed in FINDINGS:
- "The one-step adder does not depend on our read-out" held only at H 2048 and 4096. At H 512 and 1024,
  the widths of every kernel-checked one-step cell, Liu & Lu is exact in no seed after one step, so the
  rules' other clause applies there: the frequency rule is part of result 2.
- "At width the choice hardly matters" held only for clean labels on 30% of the table; with wrong labels
  or 2% of the table a random frequency fails at H 4096.
- Guess 4's "failed narrowly" hid that rounding made t* later in 14 runs, including the 2% seed-2 "-"
  under ours, which is a rounding loss (float exact from step 500).
- The DC drift under Adam was stated as measured; it is an explanation (only the DC counts are measured).
- Gaps are read on the checkpoint grid (every step to 10, coarser after): 24 of the 29 guess-2 failures
  are certainly more than 2 steps apart, five could be within 2.
- "The weakest carry none": the least energetic reading is near chance after one step but not at chance
  (8,834 to 9,231 wrong at H 4096) and reaches 7,139 wrong at best; it is never exact.
- The W2-alone explanation is isolated by `ll_nodc` against `ours_float` (both float, no DC; for x^2 the
  one-row wave is half the two-row one, a uniform factor), which FINDINGS now cites.

## Prior art for the two new observations

(a) Random frequency per neuron after one step: partly known. He et al. 2602.16849 (Sec. 3.2,
Observations 5 and 6, Fig. 4) and Wang et al. 2610.11833 (Sec. 4.1) pull every frequency of every neuron
toward the phase-sum rule at once, at a rate set by its amplitudes, which predicts that a random frequency
works and the weakest lags; both assume small initialization and many steps. Gromov 2301.02679 (Sec. 3.1)
and Swaroop 2603.23784 (Table 1) show hand-built nets with one frequency per neuron and random phases
obeying the sum rule reading out at width. Not found: reading trained weights at a random or least
energetic frequency per neuron, at any step.

(b) DC capture of the per-neuron arg max: the parts are known, the combination is not. Under gradient
descent an output column's sum over classes is conserved, because the softmax ignores a common shift
(Kunin et al. 2012.04728, Sec. 4, Eq. 11; for modular addition He et al. 2602.16849, Eqs. 5.3-5.4).
Sign-like updates do not scale with how often a class is a label (Kunstner et al. 2402.19449, Sec. 3.1).
No paper says Adam moves that column sum, or that the zero frequency then wins a per-neuron largest-bin
filter. Liu & Lu never mention k = 0 and release no code, so excluding it is an equally faithful reading;
FINDINGS reports both.

The new Open question (why the network is at chance while one random frequency per neuron reads out as an
adder) is not answered by the published theory, which assumes small initialization where the other
frequencies stay negligible (Wang et al. Thm. 1; He et al. Thm. B.4); Gromov's accounting of the x^2 terms
(Sec. 3.1, Eqs. 10-11) covers single-frequency neurons only.

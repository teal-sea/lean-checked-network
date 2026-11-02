# Eleventh batch: independent checks (2026-11-02)

## Liu & Lu's filter, implemented three times

Two agents read Liu & Lu 2026 (arXiv 2605.18022, Section 2, Section 4 and Appendix D.1) and each wrote its
own implementation of the per-neuron frequency filtration, without seeing `filters.py`, its outputs or the
eleventh batch's rules. Both read the paper the same way: the frequency is the arg max over all P DFT rows
(DC included) of |DFT| of the output weights w_m alone; P_G,m = F^H F_G(w_m) is applied to u_m, v_m and w_m;
real part; no scaling; the bias mu is kept in both sub-networks, so on bias-free nets there is nothing to
carry. Keeping one row (the paper's singleton reading) or both rows k and P - k gives the same wrong counts
on these bias-free x^2 nets: the one-row version is half the two-row wave for k >= 1, and a DC neuron is
constant over c. One agent also built the 97 x 97 matrix F explicitly and found the same numbers.

Checkpoints: train_act.py, x^2, p 97, frac 0.3, lr 0.01 (H 1024 seed 0 and H 512 seed 0, steps 0 to 3; H 1024
seed 0 with 70 tokens never seen, steps 0 and 15). The step-1 and step-15 tables equal the seal inputs
`x2_H1024_s0_step1.npz` and `x2_ht70_H1024_s0_step15.npz`. Wrong pairs out of 9,409; DC = neurons that
Liu & Lu's rule sends to k = 0; agree = share of neurons where the two rules pick the same frequency on the
frozen tables. The three implementations agree on every number below (0 mismatches).

| run | step | Liu & Lu | DC | ours, float | ours, as sealed | agree |
| --- | --- | --- | --- | --- | --- | --- |
| H 1024 s0 | 0 | 9,348 | 53 | 9,380 | 9,372 | 0.299 |
| H 1024 s0 | 1 | 11 | 48 | 0 | 0 | 0.250 |
| H 1024 s0 | 2 | 0 | 33 | 0 | 0 | 0.302 |
| H 1024 s0 | 3 | 0 | 27 | 0 | 0 | 0.325 |
| H 512 s0 | 0 | 9,302 | 20 | 9,302 | 9,216 | 0.242 |
| H 512 s0 | 1 | 785 | 18 | 7 | 12 | 0.193 |
| H 512 s0 | 2 | 27 | 18 | 0 | 0 | 0.182 |
| H 512 s0 | 3 | 10 | 14 | 0 | 0 | 0.191 |
| 70 tokens unseen, H 1024 s0 | 0 | 9,348 | 53 | 9,380 | 9,372 | 0.299 |
| 70 tokens unseen, H 1024 s0 | 15 | 458 | 660 | 0 | 0 | 0.277 |

One agent also ran Liu & Lu with DC excluded (H 1024: 9,356, 6, 0, 0; H 512: 9,305, 688, 14, 6; 70 tokens:
9,356, 20), the same as `filters.py`'s `ll_nodc`. Its observation on DC: a frequency's energy is split
between bins k and P - k while DC sits in one bin, so a DC component needs only half the energy of the best
frequency pair to win the paper's arg max. At step 15 with 70 tokens unseen, 660 of 1,024 output columns
pick DC although the median DC share of a column's energy is 5.5%.

A third agent reviewed `filters.py` against the paper (no defect: `ll` is the published filter, the other
readings do what the docstring says, the integer evaluation in float64 is exact) and `summarize_batch11.py`
against RULES.md. It found two scoring defects (readings looked up under the wrong column names; guesses 2
and 3 scored on fewer runs than their wording covers), fixed before any result of the batch was read
(commit fa7db28).

## Random frequencies: fresh draws

`rand` uses one draw per run (generator 1000 + seed). Ten more draws (generators 50,000 to 50,009) on two
checkpoints rerun locally, wrong pairs out of 9,409:

| checkpoint | ten draws |
| --- | --- |
| H 4096 seed 0, step 1 | 18, 0, 0, 0, 1, 0, 1, 0, 0, 0 |
| H 2048 seed 0, step 5 | 1, 0, 1, 4, 0, 1, 0, 0, 0, 0 |

So the batch's random-frequency result is typical, not a lucky draw: one step at H 4096 with a random
frequency per neuron is exact in 7 of 10 draws and within 18 pairs in all.

# Circle-curve experiments, 2026-10-31

Record of one day's experiments on Gromov's two-layer x² MLP for (a + b) mod p, rewritten the same
evening after an adversarial review (three independent refuters: the Lean seal, the methodology,
the novelty). Every number below is either *measured* (NumPy on integer-frozen weights, the same
evaluation rule the Lean definition uses) or *kernel-checked* (a theorem Lean's kernel accepted,
listed in the last section). The word for each is said each time.

## The question

The standard explanation of this network is the clock: each hidden neuron is one Fourier wave, and
the network adds by rotating on a circle. `circle_only.py` turns the explanation into a network:
per neuron, keep only the dominant wave (by energy summed over the three weight tables) in all three
tables, round to integers. We asked when that reduced network gives the same answers as the trained
one, across weight decay, training fraction, width, modulus, seed and training time.

## What was run

- `train_ckpt2.py`: the repo's `train.py` (AdamW-style decoupled weight decay, softmax
  cross-entropy, lr 0.01, init N(0, 1)/sqrt(H)) with dense checkpoints; `EARLY=1` adds steps 5
  to 75; `SHUFFLE_LABELS=1` permutes the training labels.
- `analyze_curve.py`: per checkpoint, wrong pairs for the frozen net and its one-wave projection,
  plus per-neuron spectrum statistics.
- `grid.txt`, 154 runs on a 32-core box: p 97, H 128, 20k steps, wd {0, 0.01, 0.03, 0.1, 0.3, 1, 3}
  x frac {0.15, 0.30, 0.50} x 5 seeds; H {64, 256} and p {53, 113, 257} subsets x 3 seeds; four
  200k-step runs (wd 0.1 and 0.03, frac 0.30, 2 seeds). `curves/`: every run's curve.
  `final_weights/`: every run's final weights. `controls/`: the shuffled-label run and the
  early-step run (p 97, H 128, frac 0.15, wd 0, seed 0). `pilot_curves/`: the 11-run pilot.
- `bias_grid.txt` + `train_bias.py`: 26 reruns with an explicit output bias (kill test, below).
- Analysis scripts, each with results beside it: `miss_map.py`, `readout_test.py`, `bias_test.py`,
  `derive_bias.py`, `kill_test.py`, `equiv.py`, `unmask.py`, `unmask2.py`.
- `seal_cell.py` + `Bridge.lean` + `seal_verdict.py`: the kernel checks, `seals/`.

All wrong counts are out of p² = 9,409 pairs unless said otherwise. Chance is 1.03% held-out.

## Results (measured)

### 1. The one-wave projection is an adder from the first twenty steps, at every weight decay

In the early-step control (frac 0.15, wd 0, seed 0) the projection is wrong on 9,244 at step 0
(chance), 1,156 at step 5, 295 at step 10, 81 at step 20 (train accuracy 47%), 54 at step 30
(94%), 36 at step 40, and between 21 and 50 from step 50 to step 2,000 while the net memorizes
(train 100%, held-out 0.5%). At step 100 the runs of a seed are still the same network across
wd 0 to 0.3 (decay applied so far is under 0.3%), so "at every weight decay" at step 100 is one
observation per seed, not seven. Across seeds at step 100 the projection is wrong on 23 to 235 at
frac 0.15, 100 to 1,600 at frac 0.3. The dominant wave carries 6 to 8% of each neuron's energy at
that point.

Controls: the shuffled-label net projects to chance at every checkpoint (9,340 to 9,376 wrong);
the init projects to chance (9,244). So the projection is label-driven. These controls do not
separate "the memorizer built an adder" from "the filter picks up the imprint of the first
gradient steps"; the early-step curve says it is the latter: the adder is written before the net
fits half the training pairs, and at wd 0 nothing removes it.

### 2. At wd 0 the projection stays an adder while the net memorizes, and the net's own held-out function is anti-aligned with addition

p 97, H 128, frac 0.15, wd 0, 20k steps, five seeds: net wrong on 7,952 to 7,970 (held-out 0.4 to
0.6%, below chance); projection wrong on 29, 78, 29, 236, 49. At H 256, frac 0.3: net wrong on
6,534 to 6,555 (held-out 0.5 to 0.8%); projection wrong on 0, 18, 13. At step 100 of the H 256 seed
0 run: net wrong on 6,559, projection wrong on 0 (gap 765,374, no ties).

Scope: at frac 0.3, H 128 the projection is wrong on 518 to 1,982; at p 113 it is wrong on ~2,500 of
12,769 and degrades over training (seed 2: 913 at step 100, 3,778 at 20k); at p 257 on 19,000 to
30,000 of 66,049; at H 64 on 3,700 to 6,200. At frac 0.5 the wd-0 nets half-generalize (held-out 38
to 48%) and the projection is wrong on 254 to 890. "Did not generalize" means within 20k steps of
AdamW cross-entropy at frac 0.3 or below; no wd-0 run was taken to 200k.

The filter matters at wd 0: choosing each neuron's frequency per table instead of by summed energy
sends the frac-0.15 projection to chance (refuter's rerun, 8,578 to 9,171 wrong), and keeping the
top two or three waves per neuron makes it worse, not better (2,495 to 4,116 and 4,854 to 5,475).
What the summed-energy one-wave filter finds is a component of 8% of the weight energy and 3 to 4%
of the logit norm.

The net's own function carries no adder on held-out inputs. Average the full net's logit table over
the translation orbits (a + s, b + t, c + s + t): over all pairs it peaks at d = 0 (the training
pairs see to that, 1.7 margins at frac 0.15), but over held-out pairs only it peaks at a random
offset and is negative at d = 0 (-0.49 to -0.59 margins, five seeds; H 256: -0.16 to -0.34). The
weights' dominant waves form an adder; the function on unseen inputs is slightly worse than chance.
Everything added back to the projection (DC, 2k, 3k, 5k harmonics) makes it worse, monotonically.

### 3. In the middle band the net generalizes and the one-wave projection does not

At frac 0.3 and 0.5 (at frac 0.15 no net generalizes below wd 1): wd 0.03, net wrong on 110 to 157
(frac 0.3) and 0 (frac 0.5), projection on 1,212 to 1,852 and 367 to 1,939; wd 0.1, net 10 to 40
and 0 to 1, projection 1,159 to 1,803 and 591 to 3,677; wd 0.3, net 2 to 18 and 0, projection 605
to 1,165 and 695 to 3,302. Five seeds each. The failure is the same under per-table frequency
choice (byte-identical projections at wd 0.1 frac 0.3) and persists with the top two or three
waves per neuron (963 to 1,351 and 688 to 1,077 at wd 0.1).

It is not unfinished cleanup. The 200k-step runs at wd 0.1: projection wrong on 1,486 and 1,260
at 200k, flat from 20k on (1,803 to 1,486, 1,159 to 1,260), while the net is at 31 and 15 and every
surviving neuron is a textbook clock neuron (dominant-wave share 94%, no multi-frequency neuron,
phases aligned; 42 of 128 neurons survive, 27 frequencies). At wd 0.03 the projection gets worse
with training (1,412 and 1,768 at 20k, 2,268 and 2,068 at 200k) while the net improves (139 to 53,
129 to 6). Float projection equals rounded projection everywhere, so this is not quantization.

At wd 1, frac 0.3, net and projection are both right (0 wrong, one seed 1). At wd 1, frac 0.15, the
projection beats the net in 4 of 5 seeds (6 to 28 wrong vs 13 to 43). At wd 3, frac 0.15, the
projection is exact in 5 of 5 while the net is wrong on 76 to 154. The earlier kernel-verified
sweep on main had already recorded the wd 3 and wd 5 cases.

So the *accuracy* of the one-wave projection is non-monotone in weight decay and decoupled from the
net's accuracy. Its *faithfulness* (does it reproduce the net) is not: at wd 0 the projection and
the net disagree on 99% of held-out pairs; it is a faithful reduction only at wd >= 1.

### 4. Where the missing piece lives, and what it is

The projection's misses in the middle band come in whole answer classes (at frac 0.5 several
residues c are wrong on all 97 pairs, the median residue on none). One-wave embeddings with the
full readout table beat the net (8, 4, 0 wrong at wd 0.1); full embeddings with a one-wave readout
fail (1,830, 1,489, 2,111). It is not DC and it is not a few extra readout waves (top 8 frequencies
per readout column still leave 34 to 43 wrong).

An adder's logit table is translation-equivariant: S[a, b, c] is a function of (c - a - b) mod p.
`equiv.py` splits the one-wave net's table into its equivariant part and the remainder, and the
remainder into a c-only part (a per-class baseline), an (a, c) part, a (b, c) part and the rest:

- The equivariant part of the one-wave net is an exact adder (0 wrong) in every cell tested,
  memorizers included (75 cells in `equiv_results.txt`, all wd, frac 0.15 to 0.5, H 128 and 256).
- In the middle band the c-only part is 0.6 to 1.3 median margins, the (a, c) and (b, c) parts 0.16
  to 0.53, the rest 0.3 to 0.9. Removing the c-only part leaves 0 to 48 wrong; removing all three
  leaves 0 to 1. At wd >= 1 every part is at most 0.24 margins, which is why the clock alone works
  there. At wd 0, frac 0.15, the parts are small (0.1 to 0.44) and the misses are few.
- The c-only part is exactly what the trained readout cancels: the readout residual (W2 minus its
  one-wave part) times the mean one-wave activation is a 97-vector whose correlation with the
  clock's baseline is -1.00 in every generalizing net. That correlation is by construction (the
  two sum to the net's own class marginal under the one-wave activation); the content is that the
  marginal is flat, within 0.05 to 0.22 margins, in every generalizing cell, while the clock's
  baseline is 0.6 to 2.0 margins at wd 0.03 to 0.3, 0.2 to 0.3 at wd 1 and 0.1 to 0.2 at wd 3.
  Adding that vector to the one-wave net gives 0 to 51 wrong per seed in every generalizing cell
  from wd 0.03 up, including p 53, 113, H 64, 256; at wd 0 frac 0.5 (held-out 38 to 48%) it takes
  the net from 2,440 to 2,931 wrong to 1 to 43.

In words: the clock is an exact adder up to its own non-equivariant artifacts; the per-class
baseline is the largest; and the structure outside each neuron's dominant wave that the net needs
in the middle band is the cancellation of those artifacts, stored in the readout's off-frequency
components. The derivation (the squared activation's constant part read through each cluster's
readout phasors; the baseline vanishes when the phasors cancel) is in the literature (see Related
work); the measurement is ours.

### 5. Kill test: train with an explicit output bias

Prediction: give the net a bias parameter (no weight decay on it) and it will put the cancellation
there; one wave per neuron plus the learned bias will explain the net; the readout junk will vanish.

- wd 0.1 and 0.3, frac 0.3 and 0.5, five seeds each: the learned bias is the negative clock baseline
  (corr 0.95 to 0.99); one wave + learned bias is wrong on 4 to 45 pairs (one seed 340) where one
  wave alone is wrong on 591 to 3,959. The readout residual's share of the readout energy drops from
  7.2 to 7.8% to 5.3 to 6.0% (frac 0.3, wd 0.1), 5.9 to 6.4% to 3.8 to 4.5% (wd 0.3), 5.2 to 7.4% to
  3.7 to 4.7% (frac 0.5): non-overlapping 5-seed ranges. So a free bias removes about a third of the
  residual's energy and nearly all of its effect on the answers; two thirds of the residual energy
  remains.
- wd 0.03, frac 0.3: one wave + learned bias is still wrong on 663 to 1,526 (net with bias 120 to
  197). The free bias absorbed only part of the baseline: adding the residual-derived bias on top
  gives 16 to 66 wrong. Same mechanism, stored in two places.
- wd 0: no effect (projection 24 to 68 wrong, the residual is memorization).
- wd 1, frac 0.15: with a bias the clock alone gets worse (43 to 243 wrong vs 6 to 28) and clock +
  bias is 0 to 3 wrong: the cancellation moved from the readout into the bias.

### 6. Training time: pruning, not reassignment

Per neuron, the dominant frequency at step 100 against the final one, among neurons alive at the
end: wd 0, 0.88 to 0.91 (all 128 survive); wd 0.1 and 0.3, 0.96 to 0.98 (42 to 51 of 128 survive,
27 to 32 frequencies); wd 1, 0.66 to 0.73 at step 100, 0.89 to 0.93 at step 500, 1.00 at step 2,000
(118 to 121 survive); wd 3, 0.78 at step 100, 1.00 at step 500. The naive statistic over all
neurons (`unmask/`) reads 0.2 to 0.5 at wd 0.03 to 0.3 only because it counts neurons that are later
pruned. So in the middle band weight decay prunes most neurons and the survivors keep the frequency
they had at step 100; at wd >= 1 few neurons die and about a quarter change frequency between
steps 100 and 500. The clock-vs-rest margin crossing in `unmask.py` does not predict the grok step
(it fires after it by a factor of about 2.5 at wd >= 1 and never at wd <= 0.3, where the "rest"
includes the bias); `unmask2.py` repeats it with the bias split out. "Grokking is unmasking" is not
claimed here: that sentence is Nanda et al.'s cleanup phase and Swaroop's "sharpens an algorithm
encoded during memorization", and the wd 1 cells show the clock being completed during grokking
(658 wrong at step 100, 94 at 500, 0 at the end), not merely revealed.

## Kernel-checked cells

`seal_cell.py` builds a fresh Lean package per cell from the repo's `Network.lean`, `Fast.lean`,
`sweep/WrongSet.lean` and `Bridge.lean`, with the trained table and the reduced table as explicit
integers, runs `lake build` (zero sorry), replays every module with `leanchecker`, prints the axioms
of every main theorem and scans the sources for forbidden tokens. Lean 4.35.0-rc2, no Mathlib.
What the kernel decides per cell: each network is wrong on exactly the listed pairs (one theorem
per row, the list strictly increasing, in range, of the stated length); the two tables have the
stated shapes; the first H columns of the reduced tables are within the stated per-mille of the
trained tables' energy (exact integer sums of squares); the extra neurons are constant (E1 = 127,
E2 = 0). What the kernel does not see: that the first H columns are each neuron's dominant wave and
that the bias columns come from the readout residual. That construction is Python
(`seal_cell.py`, `clock_bias`) and is the chain's one measured link.

| cell (hermes-ovh, 2026-10-31) | trained wrong | clock + bias wrong | disagree on | bias neurons | energy outside the wave, stated (E1, E2, W2) |
|---|---|---|---|---|---|
| p 97, H 128, frac 0.30, wd 0.1, 200k steps, seed 0 | 31 | 10 | 39 pairs (both wrong on 2) | 3 | 56, 59, 76 per mille |
| p 97, H 128, frac 0.50, wd 0.1, 20k steps, seed 0 | 0 (`adds_mod_97`) | 0 (`adds_mod_97`) | 0 | 5 | 27, 25, 69 per mille |
| p 97, H 128, frac 0.30, wd 0.3, 20k steps, seed 0 | 18 | 4 | 21 pairs (both wrong on 1) | 4 | 60, 61, 65 per mille |

Each: build completed with zero sorry warnings, 43 of 43 modules replayed by `leanchecker` (which
prints a message and exits non-zero on any problem; all logs are empty), 16 (or 12) main theorems
on propext, Classical.choice, Quot.sound or no axioms, no forbidden token. Record: the first run's
own axiom parser failed on Lean's line-wrapped output, so each `result.json` carries
`first_run_ok: false` and the verdict re-derived from the logs by `seal_verdict.py`
(`verdict.ok: true`). The disagreement counts are measured, not sealed; the clock-only table (no
bias neurons) is not sealed in these three cells; no negative control (a doctored list that the
kernel must reject) has been run on these packages yet. Pending on the Mac: the pure one-wave
projection of the p 97, H 256, wd 0, step-100 net (net wrong on 6,559, projection on 0).

## Status of each claim (the certainty ladder)

| claim | status |
|---|---|
| each trained table is wrong on exactly k pairs (per cell) | kernel-checked for 3 cells; measured for the rest |
| the clock + bias table is wrong on exactly k pairs (per cell) | kernel-checked for 3 cells; measured elsewhere, two independent evaluators agree |
| the reduced tables are within x/1000 of the trained tables' energy, extra neurons constant | kernel-checked for the same 3 cells |
| the first H columns are each neuron's dominant wave; the bias construction | measured (Python FFT); the one step the kernel does not see |
| the one-wave projection's equivariant part is an exact adder | measured, 75 cells, 0 wrong in all |
| the clock's non-equivariant artifacts are what the readout cancels; the c-only part is the largest | measured; clock minus c-only 0 to 48 wrong, minus all three 0 to 1, in 35 middle-band cells |
| an explicit bias absorbs the cancellation | measured: nearly all of its effect on answers at wd 0.1 to 0.3, a third of its energy; partly at wd 0.03 |
| the projection's accuracy is non-monotone in wd under this filter | measured, 5 seeds; the wd-0 dip is filter- and fraction-dependent, the middle-band failure is not |
| a wd-0 memorizer's dominant waves form an adder while its held-out function is anti-aligned | measured (p 97, H 128 and 256, frac <= 0.3); H 256 step 100 sealing |
| the adder is written in the first 20 steps | measured, one seed (`controls/early_*`) |

## Related work

- Nanda, Chan, Lieberum, Smith, Steinhardt 2023 (arXiv 2301.05217): the Fourier clock, progress
  measures, restricted and excluded loss; cleanup "removes the memorization components"; App. D.1
  reads wd 0 as "does not form the circuit" from a flat excluded loss. Our projection is a
  weight-space argmax measure; their loss-based measures read the same weights as no circuit.
- Gromov 2023 (2301.02679): the x² MLP, the analytic solution, destructive interference of the
  other waves. Doshi, Liao, Gromov 2023 (2310.13061) App. I.2: "cancellation of sub-leading terms",
  by low-IPR neurons at small wd and by secondary peaks at large wd, with "little effect on
  accuracy" at their width. Here it is accuracy-level (1 in 7) at H 128.
- Morwani et al. 2023 (2311.07568): max-margin solution is one frequency per neuron with cancelling
  phase pairs; the flat-marginal condition. He et al. 2026 (2602.16849) Def. 4.1(iii): the
  phase-sum condition. Tian 2024 (2410.01779) Cor. 5: a bias in the off-frequency readout entries.
- Swaroop 2026 (2603.23784): an idealized one-frequency model built from a memorization checkpoint
  (81%) and from a never-grokking model (95.5%), ReLU, wd 1 only. The closest prior statement to
  result 2; ours is at wd exactly 0, from the actual weights, with the held-out anti-alignment and
  the early-step timing.
- Varma et al. 2023 (2309.02390): coexisting memorizing and generalizing circuits, efficiency.
  Barak et al. 2022 (2207.08799): hidden Fourier-gap progress invisible to loss and error.
- Zhong et al. 2023 (clock and pizza), Kumar et al. 2023, Lyu et al. 2023, Liu et al. 2022, Prieto
  et al. 2025: grokking without weight decay occurs under other losses and optimizers; the wd-0
  memorization here is a property of AdamW + cross-entropy at this horizon.

Honest novelty sentences. (A) At weight decay exactly 0, p 97, H >= 128, frac <= 0.3, the
per-neuron dominant-wave projection of the actual weights is an adder from step 20 to step 20k
while the net's held-out function is anti-aligned with addition; Nanda et al. read this regime as
"no circuit" with loss-based measures, Swaroop never ran wd 0. (B) In the middle band the structure
outside each neuron's dominant wave that the net needs is the cancellation of the clock's own
non-equivariant terms, a per-class 97-vector first, stored in the readout's off-frequency
components; without it 1 in 7 answers flip at H 128, and an explicit bias parameter absorbs most
of it. (C) The one-wave projection's accuracy is non-monotone in weight decay and decoupled from
the net's accuracy; it is a faithful reduction of the trained net only at wd >= 1. None of this is
a paradigm shift; it is a measured, partly kernel-checked account of one reduction of one
architecture.

## Open

- A negative control on the sealed packages (drop a wrong pair, lower a per-mille bound, change an
  extra-column entry; the kernel must reject each).
- Sealing a clock-only table beside clock + bias, and the pairwise agreement of two answer
  functions, so "clock alone wrong on 1,486, clock + bias wrong on 10" is one kernel-checked pair.
- Whether the same artifact-cancellation account holds in the repo's transformer. Untested.

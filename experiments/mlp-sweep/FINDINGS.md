# MLP sweep, 2026-11-01

Follow-up to `experiments/circle-curve/FINDINGS.md`, whose headline (a weight-decay-0 memorizer
whose per-neuron dominant waves form an exact adder) was one kernel-checked seed at H 256. Rules
for every run here were written in `RULES.md` (and in each script's header) before the runs.
Every number is *measured* (NumPy, the integer evaluation rule of `lean/LeanCheckedNetwork`)
unless the word *kernel-checked* is used.

Model and training, unchanged from the circle-curve grid: Gromov's MLP for (a + b) mod p, one-hot
inputs, E1[a] + E2[b], activation x^2 (or ReLU), read-out W2, no biases; AdamW-style decoupled
weight decay (here 0), lr 0.01, betas 0.9 / 0.98, init N(0, 1)/sqrt(H), full batch, 8-bit
freezing. The *projection* is circle_only.py's: per neuron, the dominant Fourier wave (energy
summed over its E1, E2 and W2 columns) in all three columns, rounded. Counts are wrong pairs out of
p^2 (9,409 at p 97); chance is about 9,312 wrong, 1.03% held-out accuracy.

## Results (measured)

### 1. From width 512, every weight-decay-0 memorizer's projection is an exact adder

p 97, frac 0.3, 20k steps, x^2:

| H | seeds | net wrong at 20k | held-out accuracy | projection wrong, every checkpoint from step 100 to 20k |
| --- | --- | --- | --- | --- |
| 256 | 10 | 6,521 to 6,555 | 0.49 to 1.03% | 0 at step 100 in 8 seeds; 0 at every checkpoint in 3 (seeds 0, 4, 8); 0 to 84 at 20k |
| 512 | 5 | 6,552 to 6,564 | 0.27 to 0.50% | **0 at all 45 checkpoints, every seed** |
| 1024 | 3 | 6,572 to 6,580 | 0.09 to 0.21% | **0 at all 45 checkpoints, every seed** |
| 512, frac 0.15 | 2 | 7,988, 7,989 | 0.11, 0.13% | **0 at all 45 checkpoints, both seeds** |

Controls: with the training labels shuffled (H 512, seed 0, x^2 and ReLU) the projection stays at
chance at every checkpoint (9,182 to 9,352 wrong). An `EARLY=1` rerun of H 512 seed 0 has the
projection exact from step 5 on (net wrong on 9,097 at step 5, 6,655 at step 20).

The nets fit every training pair and are below chance on held-out pairs; the winning gaps of the
projections are in the millions (3.0 to 3.9 million at 20k for H 512), no ties. At initialization
the projection is at chance (9,057 to 9,390 wrong). The circle-curve grid's earlier H 256 seeds 1
and 2 (18 and 13 wrong at 20k) sit at the transition width.

### 2. One Adam step writes the adder; the network is still at chance

Checkpoints at steps 1 to 5 (`first_steps.sh`, `EXTRA_STEPS`), p 97, frac 0.3, lr 0.01, x^2:

| H | first step with projection wrong on 0 (seeds 0, 1, 2) | net wrong at that step |
| --- | --- | --- |
| 256 | 4, 6+ (1 wrong at step 5), 4 | 9,064 to 9,124 |
| 512 | 2, 2, 2 (12, 97, 85 wrong at step 1) | 8,997 to 9,129 |
| 1024 | 1, 1, 1 | 8,974 to 9,132 |
| 2048 | 1, 1, 1 | 8,970 to 9,040 |

**How often** (`first_steps4.sh`, 20 seeds per width, lr 0.01; `results/first_steps4_seeds.log`):
exact at step 1 in 19 of 20 seeds at H 768 (the twentieth wrong on 1 pair, exact at step 2) and in
20 of 20 at each of H 1024, 1536 and 2048, exact again at step 2 in all 80 runs, while the nets are
wrong on 8,803 to 9,169 pairs at step 1.

After one step an H 1024 net fits 9 to 15% of its training pairs and is below chance on held-out
pairs (0.09 to 0.49%), and its projection is right on all 9,409 pairs.

Neither part alone carries it (`update_only.py`): the initialization projects to chance, and the
first update alone (step-1 weights minus step-0 weights, frozen the same way) projects to chance
too (9,138 to 9,308 wrong at H 512 to 2048). Only their sum does.

**Moduli** (`first_steps2.sh`, frac 0.3, H 1024 and 2048, seeds 0-2): exact at step 1 for p 31
(5 of 6; the sixth at step 2), 61, 113, 127 (6 of 6 each) and 257 (H 1024 seeds 0-1 so far),
while the nets are at chance (p 257: 65,416 of 66,049 wrong).

**Learning rate** (`first_steps3.sh`): the first exact step t* follows t* x lr x H of about 10,
within one step, for H >= 512 (18 runs: H 512 at lr 0.02 -> 1, 1, 1 (predicted 1) and lr 0.005 ->
3, 4, 4 (4); H 1024 at lr 0.005 -> 1, 2, 2 (2) and 0.0025 -> 2, 3, 3 (4); H 2048 at lr 0.0025 ->
2, 2, 2 (2) and 0.00125 -> 3, 3, 3 (4)). It fails at H 256 with large steps (lr 0.04: 4, 2, 5
against 1), where a step is no longer small against the initialization (lr x sqrt(H) = 0.64).

**Plain gradient descent** (`sgd_one_step.sh`: `train_gen.py` with `OPT=sgd`, full batch, no momentum
and no per-coordinate scaling, lr = c x H, seeds 0-2; `results/sgd_one_step.log`): with c = 3 the
projection is exact at step 1 in all 9 runs (H 512, 1024 and 2048). With c = 1 it is exact at step 1
in 4 of 6 runs at H 1024 and 2048 (the other two are wrong on 1 pair and exact at step 2) and at
step 2 in 1 of 3 at H 512 (5 and 14 wrong in the others). With c = 0.3 no run is exact at step 1;
H 2048 is exact at step 2. A finer scan at H 1024, seed 0 (`results/sgd_lr_scan_H1024.log`): lr 1
and 10 stay at chance for 3 steps, lr 100 gets to 5,156 wrong at step 3, lr 1,000 is exact at steps
1, 2 and 3, and lr 10,000 is wrong on 127 at step 1, on 0 at step 2 and on 9,242 at step 3, where
the run diverges. The nets stay near chance in all of these (8,548 to 9,318 wrong). So Adam's
per-coordinate normalization is not needed: one ordinary gradient step of size about H writes the
adder, with an upper edge near 10 H.

Why, as a sketch (not a proof): write each weight as initialization plus update. In the
projection's logit for class c the terms with one update factor and two initialization factors
have phases summing to zero for c = a + b, because the first gradient is a correlation of the other
two random tables (for E1: W2 against E2; for W2: E1 convolved with E2). Inside one neuron's
dominant wave these aligned terms add coherently over H neurons, while the initialization-only
terms (random phases) add like sqrt(H); the signal-to-noise ratio grows like t x lr x H, which is
the law above.

### 3. ReLU: the memorizer is wrong on every held-out pair; its projection is nearly an adder

Same runs with max(x, 0) in place of x^2:

| H | seeds | net wrong | held-out pairs right | projection wrong at 20k (with bias) |
| --- | --- | --- | --- | --- |
| 256 | 5 | 6,585 to 6,586 | 0 or 1 of 6,586 | 754 to 1,309 (592 to 1,048) |
| 512 | 3 | 6,586 | **0 of 6,586** | 7, 37, 67 (7, 31, 52) |
| 1024 | 3 | 6,586 | **0 of 6,586** | **0, 0, 0** (seeds 0 and 2: 0 at all 45 checkpoints from step 100; seed 1: 0 or 1) |
| 2048 | 1 | 6,586 | **0 of 6,586** | **0 at all 45 checkpoints** |
| 256, wd 1 (control) | 2 | 0, 1 | all | 0, 1 |

So from width 1024 a ReLU network that is wrong on every single held-out pair, and right on every
training pair, has one-wave projection that is an exact adder on all 9,409 pairs.

Chance would be about 68 held-out pairs right. The mechanism (measured on H 512 seed 1): on
99.98% of held-out pairs the net's answer is a label of some training pair in the same row a or the
same column b, and (a + b) mod p is never such a label, since a + b' = a + b forces b' = b. The x^2
memorizers do the same on 90.6 to 91.4% of held-out pairs, which is why their held-out accuracy is
below chance. ReLU writes the adder more slowly than x^2: at step 5, H 1024 is still wrong on 63
and 130; an `EARLY=1` rerun of ReLU H 512 seed 1 goes 2,100 (step 5), 541 (10), 100 (20), 31 (30),
6 (100).

### 4. The transformer does not do this

See `experiments/transformer-curve/FINDINGS.md`: under every reduction fixed in advance, Nanda et
al.'s one-layer transformer at weight decay 0 has no adder near exact (7,400+ wrong).

### 5. Other activations: |x| writes the adder too; tanh does not; GELU and SiLU not by 20k

Batch 3 (`jobs_A3.txt`, `jobs_B3.txt`; rule and prediction in their headers and in `train_gen.py`):
H 1024, seeds 0 and 1, 20k steps, otherwise as above. The projection here is the float one
(`analyze_gen.py`: the same construction without the 8-bit rounding, which is not meaningful for
activations that are not scale-invariant).

| activation | net wrong at 20k | held-out accuracy | projection wrong, step 100 to 20k (44 checkpoints) |
| --- | --- | --- | --- |
| \|x\| | 6,572, 6,572 | 0.21% | **0 at every checkpoint, both seeds** |
| tanh | 6,586, 6,586 | 0 of 6,586 | 9,291 to 9,323 at every checkpoint (chance) |
| GELU (tanh approximation) | 6,586, 6,586 | 0 of 6,586 | 6,502 down to 3,575; 6,986 down to 3,771 |
| SiLU | 6,586, 6,586 | 0 of 6,586 | 7,684 down to 5,761; 8,240 down to 6,355 |

Early steps (seed 0, steps 1 to 5): the |x| projection is wrong on 711, 29, 0, 0, 0 (exact from step 3,
with the net wrong on 8,933); GELU, SiLU and tanh stay at chance (9,311 to 9,336).

The prediction fixed before the runs ("GELU, SiLU and abs behave like x^2 and ReLU; tanh fails")
held for |x| and tanh and failed for GELU and SiLU at 20k. GELU and SiLU are not a null like tanh:
their projections fall at almost every checkpoint and had not leveled off at 20k. A reading, not yet
tested: at initialization a pre-activation is about sqrt(2/H) = 0.044, where GELU is about
z/2 + 0.40 z^2 and SiLU about z/2 + 0.25 z^2, so the odd part is about 28 and 45 times the even part.
tanh has no even part, |x| is all even part, and ReLU = (z + |z|)/2 is half and half at every
scale. The outcomes line up with the size of the even part (|x| exact at H 1024 from step 3, ReLU
exact from H 1024, GELU then SiLU partial, tanh at chance), and the falling GELU and SiLU counts fit
pre-activations that grow as the weights grow at weight decay 0.

Every one of these memorizers fits all training pairs from step 100 on. GELU, SiLU and tanh, like
ReLU, are wrong on every held-out pair (6,586 of 6,586) at every checkpoint from step 100: the
row/column exclusion of result 3 does not depend on the activation. The |x| nets are below chance
(0.05 to 0.26%) but not at 0.

### 6. |x| from width 512 (fourth batch A)

Rules in `RULES.md` (fourth batch, A), run on GitHub Actions (`sweeps/batch4.txt`); curves in
`results/batch4/`. |x|, p 97, frac 0.3, 20k steps; the integer projection of `analyze_act.py`, the
quantity a seal checks, at the 44 checkpoints from step 100 to 20k:

| H | seeds | net wrong at 20k | held-out accuracy, highest from step 100 | projection wrong, 44 checkpoints |
| --- | --- | --- | --- | --- |
| 256 | 3 | 6,525 to 6,542 | 0.74 to 1.02% | never 0: 2 to 27 (9, 6, 25 at 20k) |
| 512 | 3 | 6,551, 6,559, 6,560 | 0.41 to 0.52% | **0 at every checkpoint, all three seeds** (no ties) |
| 1024 | seed 2 | 6,569 | 0.24% | 0 at every checkpoint, and from step 3 |

The prediction fixed before the runs (exact at H 512 for every seed) held. At H 512 the projection is
wrong on 1 to 25 pairs at step 5 and exact at the next checkpoint, step 100. The shuffled-label control
(H 512, seed 0) memorizes its labels and its projection stays at 9,219 to 9,308 wrong at all 51
checkpoints, inside the range of untrained projections (9,226 to 9,388 at step 0). With the
baseline-cancelling bias, H 256 seeds 0 and 1 are exact from step 100 too (seed 2: 0 to 5). Seeds 0 and
1 at H 1024 (third batch) were measured with the float projection only (exact at every checkpoint).

### 7. The even part of the activation writes the adder and reads it (fourth batch B)

f(s z) / s for GELU and SiLU at s = 1, 3, 10, 30, 100 and tanh at s = 1, 10, 100, H 1024, 2,000 steps
(GELU seeds 0 and 1, SiLU and tanh seed 0), and plain GELU (s = 1, seed 0) to 20k. s reads the same
activation at s times the pre-activation, so the weights, init and optimizer do not change. r is the
size of the even part against the odd part at initialization, computed before the runs. The float
one-wave projection (`analyze_gen.py`) is read with the network's own activation, and by
`analyze_even.py` with z^2 and with |z| (the even part of GELU or SiLU gives the same counts as z^2 in
every run, so z^2 and |z| are the two independent readouts). t* = first checkpoint from which the count
stays 0 to step 2,000.

| run | r | own readout wrong at 1,000 / 2,000 | t* own readout | t* read with z^2 / with \|z\| |
| --- | --- | --- | --- | --- |
| SiLU, s = 1 | 0.028 | 6,501 / 6,139 | none | 50 / 50 |
| GELU, s = 1 (2 seeds) | 0.044 | 4,460 to 4,909 / 4,137 to 4,424 | none | 20 / 20 |
| SiLU, s = 3 | 0.083 | 788 / 604 | none | 20 / 20 |
| GELU, s = 3 (2 seeds) | 0.131 | 32 to 69 / 16 to 37 | none | 10 / 20 |
| SiLU, s = 10 | 0.265 | 0 / 0 | 50 | 2 / 5 |
| GELU, s = 10 (2 seeds) | 0.404 | 0 / 0 | 50 | 2 / 4 to 5 |
| SiLU, s = 30 | 0.620 | 0 / 0 | 20 | 2 / 3 |
| GELU, s = 30 (2 seeds) | 0.798 | 0 / 0 | 10, 50 | 1 to 2 / 4 |
| SiLU, s = 100 | 0.928 | 0 / 0 | 600 | 2 / 4 |
| GELU, s = 100 (2 seeds) | 0.975 | 0 / 0 | 50, 1,000 | 2 / 4 to 5 |
| tanh, s = 1, 10, 100 | 0 | 9,297 to 9,315 / 9,297 to 9,305 | none | none / none (9,182 to 9,403) |

Every one of these networks fits its training pairs from step 100 on and is wrong on all 6,586
held-out pairs. The four predictions fixed before the runs:

1. The own-readout count falls as r rises, GELU and SiLU on one ordering: held (monotone where it is
   above 0; 9 of the 15 runs tie at 0).
2. "Exact only where r is at least 0.9, and there from step 100": failed both ways. Every run with r
   from 0.265 up is exact at steps 1,000 and 2,000, and two of the three runs with r above 0.9 have
   single-pair misses after step 100 (GELU s = 100 seed 1 at steps 200, 600, 800 and 900; SiLU s = 100
   at step 500).
3. tanh at chance at every s: held, under every readout.
4. The odd part alone at chance: held in every run. For GELU and SiLU the odd part is exactly z/2,
   whose class scores have the form U(a, c) + V(b, c) and so can never add; this is a sanity check.

Not predicted (the readouts were fixed in advance, their outcome was not): **read with z^2 or |z|, the
projection is exact in every GELU and SiLU run and stays exact**, from step 20 for plain GELU and step
50 for plain SiLU, while read with their own activation it never is. For the GELU memorizer run to
20k, the z^2 readout is exact at all 44 checkpoints from step 100 to 20k while its own readout is
wrong on 3,575 to 6,502 pairs. For tanh the same readouts stay at chance. It is the one-wave
projection that adds: the unprojected GELU and SiLU nets read with z^2 or |z| are wrong on 6,510 to
6,561 pairs, no better than as memorizers.

Reading (an interpretation): the even part of the activation writes the adder into each neuron's
dominant wave, the odd part writes nothing (tanh), and at read-out the odd part's additively separable
scores mask an adder that is already there (GELU, SiLU). Post hoc, for the four runs with r at most
0.131, the first step from which the z^2 readout stays exact fits t* x lr x H x r of about 9 (the
intervals the checkpoint grid allows overlap at 8.5 to 9.0); larger r is faster than that. The sixth
batch tests this law on activations it was not fitted on.

The GitHub rerun of plain GELU (s = 1, seed 0) reproduces the third batch's box run at all 45 common
checkpoints. A second rerun with checkpoints kept (`sweeps/gelukeep.txt`, `int_even.py`) shows the same
for the sealable quantity: the 8-bit integer projection of the GELU weights, read with z^2, is exact
with no ties at steps 20, 50, 100, 2,000 and 20,000 (SiLU: from step 20), while the frozen weights
themselves read with z^2 are wrong on 6,517 pairs at 20k. Seals are running.

### 8. How little data one step needs (fourth batch C)

x^2, frac 0.05 to 0.3, H 512 to 4096, seeds 0-2, 500 Adam steps, integer projection. t* = first
checkpoint (steps 1 to 10, 15, 20, 30, 50, 75, then every 100) from which the projection is wrong on 0
pairs to step 500; - means it never settles (with the smallest count).

| frac (training pairs) | H 512 | H 1024 | H 2048 | H 4096 |
| --- | --- | --- | --- | --- |
| 0.05 (470) | 20, - (1), 30 | 10, 20, 20 | 5, 15, 10 | 6, 9, 8 |
| 0.075 (706) | 20, 20, 30 | 7, 15, 15 | **1**, 8, 5 | **1**, 7, 5 |
| 0.1 (941) | 15, 15, 15 | 10, 15, 2 | **1, 1, 1** | **1, 1, 1** |
| 0.15 (1,411) | 15, 15, 9 | **1**, 2, **1** | **1, 1, 1** | **1, 1, 1** |
| 0.2 (1,882) | 15, 3, 4 | **1, 1, 1** | **1, 1, 1** | **1, 1, 1** |
| 0.3 (2,823) | 2, 2, 2 | **1, 1, 1** | **1, 1, 1** | **1, 1, 1** |

The win fixed in advance (exact after one step at frac 0.1 or below, at any H up to 4096) is met:
**one Adam step on 10% of the table gives an exact projection at H 2048 and 4096 in all three seeds**,
and on 7.5% in seed 0 at both widths. At frac 0.3 the law t* x lr x H of about 10 is reproduced (t* 2
at H 512, 1 at H 1024). The work t* x lr x H grows faster than 1/frac: a log-log fit over the finite
cells gives an exponent of 1.37 (1.53 leaving out the cells at the t* = 1 floor, which only bound the
work from above; 0.9 to 1.9 by width), steeper than both simple pictures (1/2 and 1). The fit's
pooling and its treatment of the floor were not fixed in advance.

**Generalization to what was never seen.** At frac 0.05 the training sets are small enough to miss
whole tokens and sums. Seed 0's 470 pairs never contain token 74 (as a or as b) nor 68 as a first
token, so training never changes the float rows of E1 and E2 for them (bit-identical to the
initialization at every kept step; only their 8-bit rounding is rescaled); seed 1's never contain a
pair with sum 83; seed 2's never contain sum 35 or first token 32. In all three the projection becomes
exact on all 9,409 pairs at H 1024 to 4096 (every checkpoint to step 500), including the 193 pairs
with token 74 and the 97 pairs with each unseen sum. The memorizing network cannot do this (its rows
for token 74 are its random initialization). The projection can because it reads each weight column in
token-index order as one wave over Z_97: the cyclic order of the tokens is built into the projection,
not learned by the network, and it is what fills in the unseen tokens.

Caveats from the independent check: for a given frac and seed every width trains on the same pairs
(the split is drawn before the init), and the subsets are nested across fractions, so a column of the
table is three training sets, not three independent draws per cell. The H 2048 and 4096 weights were
not kept; those cells rest on the runner's curves (the runs are deterministic and can be redone).

### 9. Wrong labels (fifth batch A)

x^2, frac 0.3, a fraction of the training labels replaced by wrong ones (`NOISE_FRAC`, drawn from a
separate generator so the initialization and the split are the clean run's), 500 steps, integer
projection scored against (a + b) mod 97 on all 9,409 pairs. t* per seed, with the prediction fixed in
advance (t* x lr x H x (1 - noise) of about 10):

| wrong labels | H 1024 (predicted t*) | H 2048 | H 4096 |
| --- | --- | --- | --- |
| 25% | 2, 1, 2 (2) | **1, 1, 1** (1) | **1, 1, 1** (1) |
| 50% | 6, 10, 6 (2) | 2, 5, 6 (1) | **1, 1**, 2 (1) |
| 75% | 15, 20, 20 (4) | 15, 15, 15 (2) | 9, 10, 9 (1) |

The win fixed in advance is met: **with half of the training labels wrong, one Adam step gives an exact
projection at H 4096 in two of three seeds** (the third at step 2). The prediction held at 25% wrong and
failed at 50% (except H 4096 seeds 0 and 1) and at 75%: wrong labels cost more than missing ones. Clean
runs with the same number of correct pairs are faster (frac 0.15, as many correct pairs as 50% noise:
t* 1, 2, 1 at H 1024; frac 0.075 against 75% noise: 7, 15, 15 against 15, 20, 20). The networks fit
their wrong labels (train accuracy 1.0 against the noisy labels by step 15 to 30; at step 500 the
8-bit nets are wrong on 7,273 to 8,671 pairs, about 6,560 plus the noisy training pairs); with 75% wrong
labels the projection becomes exact while that fitting is under way and stays exact to step 500 while
the network memorizes the wrong labels. No shuffled-label control was run at these widths.

### 10. Width against modulus (fifth batch B)

x^2, frac 0.3, p 31 to 257, H 256 to 768, seeds 0-4, steps 1 to 5 only (t* above 5 is censored), integer
projection. t* per seed (> 5: not exact by step 5):

| p | H 256 | H 384 | H 512 | H 768 |
| --- | --- | --- | --- | --- |
| 31 | > 5 in all 5 | > 5, > 5, > 5, 2, 4 | 5, 2, 3, 2, 2 | 2, 2, 1, 1, 4 |
| 61 | 5, > 5, > 5, 4, > 5 | > 5, 2, 3, 2, 3 | 2, 3, 2, 2, 2 | 1, 2, 2, 2, 1 |
| 127 | > 5, > 5, 5, 4, > 5 | 2, 3, 3, 2, 2 | 2 in all 5 | **1 in all 5** |
| 257 | > 5, > 5, > 5, 4, 5 | 3, 3, 3, 2, 2 | 2 in all 5 | **1 in all 5** |

The prediction fixed in advance (t* 4, 3, 2, 2 at the four widths, the same for every p within one
step) holds for 60 of the 80 runs. It fails at H 256 for every p (14 of 20 runs not exact by step 5)
and for p 31 at the larger widths. The width needed does not grow with p from 31 to 257; the small
moduli are the harder ones. At frac 0.3 small p also means few pairs per residue (0.3 p: 9 at p 31,
77 at p 257), which this batch cannot separate from p itself.

### 11. When the hidden adder arrives: a law that holds for GELU at every width and fails for z^2 + c z (sixth batch)

Rules in `RULES.md` (sixth batch), fixed before the runs. p 97, frac 0.3, H 1024 unless stated, 300
Adam steps, checkpoints at every step to 20, every 2 to 40, every 5 to 100. t* = first checkpoint from
which the float projection read with z^2 is exact to step 300; predicted t* = 9 / (lr x H x r), with r
the even part's size at initialization (the post-hoc law of result 7). Seeds 0 and 1:

| activation | r | predicted t* | measured t* | own readout wrong at 300 |
| --- | --- | --- | --- | --- |
| GELU, H 512 | 0.062 | 28.2 | 24, 26 | 5,626, 6,594 |
| GELU, H 1024 (fourth batch, coarser grid) | 0.044 | 19.9 | 11 to 20, both seeds | 6,291, 6,845 (at 200) |
| GELU, H 2048 | 0.031 | 14.1 | 14, 13 | 6,017, 6,600 |
| GELU, H 4096 | 0.022 | 9.9 | 10, 9 | 7,316, 7,135 |
| tanh(z) + d z^2, d = 0.5 | 0.028 | 31.7 | 17, 17 | 8,288, 8,427 |
| d = 1 | 0.055 | 15.8 | 13, 12 | 6,388, 7,148 |
| d = 2 | 0.111 | 7.9 | 9, 8 | 2,415, 2,888 |
| d = 4 | 0.222 | 4.0 | 3, 3 | 15, 32 |
| d = 10 | 0.555 | 1.6 | 1, 1 | 0, 0 |
| z^2 + c z, c = 0.25 | 0.222 | 4.0 | 3, 3 | 0, 0 |
| c = 0.5 | 0.111 | 7.9 | 10, 10 | 1,189, 1,590 |
| c = 1 | 0.055 | 15.9 | 13, 12 | 6,467, 7,108 |
| c = 2 | 0.028 | 31.7 | **15, 14** | 8,590, 8,695 |
| c = 4 | 0.014 | 63.5 | **16, 16** | 9,066, 9,096 |
| c = 8 | 0.007 | 126.9 | **24, 22** | 9,213, 9,206 |
| controls: z^2 + 0 z; tanh at H 4096 | | 1; never | 1; never (z^2 readout 9,240 or more) | 0; 9,319 |

Prediction 1 (within a factor 2 for every run with r at most 0.15) held in 8 of the 11 seed-0 runs, short
of the 9 fixed as the win: **the law failed for z^2 + c z at c = 2, 4 and 8**, where the adder arrives at
step 15 to 24 instead of growing like c. It held for every GELU run, and there quantitatively: the
predicted fall like 1/sqrt(H) (28, 20, 14, 10) matches the measured 24 to 26, 20, 13 to 14 and 9 to 10.
(The H 1024 point was in the fit that set the constant 9, so the width scaling is tested by H 512,
2048 and 4096.) Prediction 2 (no slower than the law for r above 0.15) held in all 6 runs. Prediction 3 (z^2 + c z and
tanh(z) + d z^2 with the same r within a factor 2 of each other) held in all four pairs, including the
pair at r = 0.028, where both arrive at about half the predicted time (c = 2: 15, 14, outside the
factor 2; d = 0.5: 17, 17, just inside). Prediction 4 (tanh never) held. All networks but the plain x^2
control memorize (wrong on all 6,586 held-out pairs at step 300; the control on 6,577), and only
z^2 + 0.25 z and tanh(z) + 10 z^2 have their own readout exact (tanh(z) + 4 z^2: 15 and 32 wrong).

What the law gets right is GELU's width scaling (measured exponent -0.42 to -0.51 against -0.5). At
fixed H 1024, t* grows with 1/r much more slowly than the law says (log-slope -0.3 for z^2 + c z and
-0.5 for tanh(z) + d z^2, against -1), so for long arrivals the law predicts later than measured. A
possible reason, post hoc and untested: by step 15 the weights have moved by about 15 x lr = 0.15 per
entry, several times the initialization scale (about 0.03), so the pre-activations, and with them the
even part's share, have grown. With the constant at 8.5, the low end of the fit's range, 9 of 11 runs
would pass; against the 9 fixed in advance, 8 do.

### 12. Exact on tokens and sums never seen in training (seventh batch)

Rules in `RULES.md` (seventh batch), fixed before the runs. x^2, p 97, the usual frac-0.3 split with
every pair removed that contains one of k held-out tokens (as a or b), or whose sum is one of k
held-out sums; 500 Adam steps; integer pure clock (what a seal checks) scored on all 9,409 pairs. t* =
first checkpoint from which it is exact on all 9,409 pairs to step 500 (three seeds):

| held out | training pairs (seed 0) | H 1024 | H 2048 | net wrong on the held-out pairs at step 500 |
| --- | --- | --- | --- | --- |
| 1 token | 2,765 | 1, 1, 1 | 1, 1, 1 | 193 of 193 |
| 3 tokens | 2,640 | 1, 1, 1 | 1, 1, 1 | 573 of 573 |
| 10 tokens | 2,286 | 1, 1, 1 | 1, 1, 1 | 1,838 to 1,840 of 1,840 |
| **30 tokens (31% of the vocabulary)** | 1,324 | **2, 2, 2** | **1, 1, 1** | 4,904 to 4,910 of 4,920 |
| 1 sum | 2,790 | 1, 1, 1 | 1, 1, 1 | 97 of 97 |
| 3 sums | 2,725 | 1, 1, 1 | 1, 1, 1 | 291 of 291 |
| 10 sums | 2,528 | 1, 1, 1 | 1, 1, 1 | 970 of 970 |
| **30 sums** | 1,981 (1,955 to 1,981 over seeds) | 15, 15, 9 | 9, 10, 7 | 2,910 of 2,910 |

All 48 runs are exact on all 9,409 pairs by step 15 and stay exact to step 500. **After one Adam step
on a training set in which 30 of the 97 tokens never occur, the projection adds correctly on all 4,920
pairs that contain one of them (H 2048, all three seeds)**, while the network itself is right on 28 to
32 of those pairs at step 1 (10 to 16 at step 500, about chance). Training never changes the float rows
for those tokens; the projection supplies them from each neuron's wave, read in token-index order (see
the remark under result 8: the order is the projection's, not the network's). With 30 sums never shown as a label the network
is wrong on all 2,910 such pairs (at H 1024 it never outputs a held-out sum on any pair at any
checkpoint) and the projection is right on all of them. Both predictions held and
the win fixed in advance (30 tokens or 30 sums, any seed) is met for both. Held-out sums are the harder
case (7 to 15 steps against 1 to 2 for tokens); for 30 sums the projection is first exact at step 1 at
H 2048 and then loses and regains exactness before t*. The eighth batch looks for where it stops.

### 13. How far it goes: exact with 70 of 97 tokens, or 80 of 97 sums, never seen (eighth batch)

Rules in `RULES.md` (eighth batch), fixed before the runs: the seventh batch's setup with k = 40 to 80
held-out tokens or sums, H 2048 and 4096, three seeds, 500 steps. t* per seed; "-" means not exact by
step 500 (with the smallest count):

| held out | training pairs | H 2048 | H 4096 | net wrong on the held-out pairs |
| --- | --- | --- | --- | --- |
| 40 tokens | 961 | 1, 2, 2 | 1, 1, 1 | 6,131 to 6,147 of 6,160 |
| 50 tokens | 663 | 4, 6, 5 | 1, 6, 5 | 7,163 to 7,173 of 7,200 |
| 60 tokens | 408 | 15, 7, 9 | 8, 6, 5 | 7,988 to 8,004 of 8,040 |
| **70 tokens** | **240** | **15, 15, 15** | **9, 15, 15** | 8,619 to 8,636 of 8,680 |
| 80 tokens | 81 | - (1), - (394), - (2) | - (1), - (130), - (5) | 9,046 to 9,063 of 9,120 |
| 40 sums | 1,676 | 15, 10, 15 | 15, 9, 15 | all 3,880 |
| 50 sums | 1,375 | 15, 20, 20 | 15, 15, 15 | all 4,850 |
| 60 sums | 1,076 | 20, 20, 20 | 15, 15, 15 | all 5,820 |
| 70 sums | 790 | 30, 20, 30 | 20, 20, 20 | all 6,790 |
| **80 sums** | **522** | **30, 50, 50** | **30, 30, 30** | all 7,760 |

**Trained on 240 pairs drawn from 27 of the 97 tokens, the projection is an exact adder on all 9,409
pairs (every seed, both widths)**, including the 8,680 pairs that contain one of the 70 tokens the
network never saw, where the network is right on 44 to 61 (chance is about 89). With 80 sums never used
as a label (522 training pairs with 17 distinct labels), the projection is exact in all six runs, while
the network outputs none of the unseen sums. The largest k exact in every seed is 70 for tokens and at
least 80 for sums, at both widths; the guess recorded in advance (50) was too low, and the win (k of 49
or more tokens, any seed) is met. At 80 tokens (17 seen, 81 training pairs) two of three seeds end 1 to
5 pairs short.

The ninth batch (`RULES.md`, fixed before its runs) placed the limit. At H 1024, 60 held-out tokens are
exact from step 15 in all three seeds and 70 from step 15 to 20 in all three (predicted: all three and
at least one). More width does not move the limit: at H 8192, 80 held-out tokens end 4, 359 and 4 pairs
short (predicted exact in at least two seeds: failed), and 85 and 90 are far off (6,890 or more wrong;
predicted). 90 held-out sums at H 4096 (7 labels seen) end 4,201 to 5,659 short (predicted exact in at
least one seed: failed). So the limit is set by the data, between 70 and 80 missing tokens (240 and 81
training pairs) and between 80 and 90 missing sums, not by the width.

### 14. Exact from 2% of the table (tenth batch)

Rules in `RULES.md` (tenth batch), fixed before the runs: plain random training sets of 1% to 3% of the
table, x^2, H 2048 and 4096, three seeds, 1,000 Adam steps, integer projection. t* per seed; "-" means
not exact at every checkpoint to step 1,000 (smallest count, count at step 1,000):

| frac (pairs) | H 2048 | H 4096 |
| --- | --- | --- |
| 0.01 (94) | - (1,696, 1,759), - (2,163, 2,269), - (560, 579) | - (838, 844), - (1,718, 2,128), - (231, 256) |
| 0.015 (141) | - (334, 557), - (286, 286), - (128, 145) | - (2, 3), - (9, 9), - (8, 67) |
| **0.02 (188)** | - (11, 174), - (0, 1), **30** | - (1, 9), **20**, - (5, 886) |
| 0.025 (235) | 30, - (8, 16), 30 | - (0, 2), 15, 20 |
| 0.03 (282) | 20, 30, 20 | 15, 15, 15 |

**From 188 random pairs, 2% of the table, the projection is an exact adder on all 9,409 pairs and stays
exact to step 1,000 (one seed at each width)**, while the network fits those pairs and is wrong on
about 9,210 of the rest. From 282 pairs (3%) every seed is exact at both widths. The win fixed in
advance (exact from at most 2%, any seed) is met; the guess (exact from 2.5% at H 4096) was about
right. At 1.5% and below no run gets there, and at these sizes the projection can be exact at one
checkpoint and lose it again while the network memorizes (H 2048, frac 0.02, seed 1 ends at 1 wrong).

## Kernel-checked

Thirty-two seals ran on GitHub Actions (`.github/workflows/seal-cells.yml`, one 4-vCPU, 16 GB runner
per cell, queues in `seal_queues/`) with the unchanged `seal_cell.py --pure-clock` for x^2 and
`seal_act.py` for ReLU (with `--right-iff-trained`) and |x| (`lean/LeanCheckedNetwork/Abs.lean`), reading the activation from the checkpoint (`--max-heartbeats` and `--chunks` change only
elaboration limits and file layout). Every verdict is ok: the build has no `sorry`, `leanchecker`
replays every module (75 of 75; 139 of 139 at H 1024; 77 of 77 and 141 of 141 for ReLU; 76 of 76 for |x|), `#print axioms` shows only `propext`,
`Classical.choice` and `Quot.sound`, and the forbidden-token scan is empty. The packages are in
`seals/` (result.json, logs and the generated Lean sources); `seal_inputs/MANIFEST.json` gives each
cell's source checkpoint and its sha256.

Each x^2 seal proves, for the integer weights in its package, that the trained net is wrong on
exactly the stated pairs (`answer_iff_not_wrong`, `wrongPairs_length`) and that its one-wave
projection adds mod 97 on all 9,409 pairs (`adds_mod_97`). How the weights were made (seed, number
of steps, optimizer) is measured provenance, not part of what is checked.

| cell | how it was made | trained net wrong | projection | smallest winning gap of the projection |
| --- | --- | --- | --- | --- |
| x2_H512_s0_final | 20k Adam steps, seed 0 | 6,552 | adds mod 97 | 3,890,477 |
| x2_H512_s1_final | seed 1 | 6,564 | adds mod 97 | 3,284,529 |
| x2_H512_s2_final | seed 2 | 6,560 | adds mod 97 | 3,672,160 |
| x2_H512_s3_final | seed 3 | 6,563 | adds mod 97 | 3,014,016 |
| x2_H512_s4_final | seed 4 | 6,559 | adds mod 97 | 3,861,987 |
| x2_H512_s0_step100 | 100 Adam steps, seed 0 | 6,563 | adds mod 97 | 4,425,284 |
| x2_H512_s0_step2 | 2 Adam steps (lr 0.01), seed 0 | 9,129 | adds mod 97 | 32,548 |
| x2_H512_s1_step2 | seed 1 | 8,997 | adds mod 97 | 23,279 |
| x2_H512_s2_step2 | seed 2 | 9,105 | adds mod 97 | 10,034 |
| x2_H512_lr002_s0_step1 | **1 Adam step** (lr 0.02), seed 0 | 9,151 | adds mod 97 | 13,413 |
| x2_H512_lr002_s1_step1 | seed 1 | 9,016 | adds mod 97 | 11,347 |
| x2_H512_lr002_s2_step1 | seed 2 | 9,116 | adds mod 97 | 8,535 |
| x2_H512_sgd1536_s0_step1 | **1 plain gradient step** (lr 1,536), seed 0 | 9,183 | adds mod 97 | 14,886 |
| x2_H512_sgd1536_s1_step1 | seed 1 | 9,122 | adds mod 97 | 6,305 |
| x2_H1024_s0_step1 | **1 Adam step at the standard lr 0.01**, H 1024, seed 0 | 9,018 | adds mod 97 | 72,595 |
| x2_H1024_s1_step1 | 1 Adam step, H 1024, seed 1 | 8,974 | adds mod 97 | 56,367 |
| x2_H1024_s2_step1 | 1 Adam step, H 1024, seed 2 | 9,132 | adds mod 97 | 64,668 |
| x2_f015_H1024_s0_step1 | **1 Adam step on 15% of the table** (1,411 pairs), H 1024, seed 0 | 9,127 | adds mod 97 | 12,641 |
| x2_f015_H1024_s2_step1 | 1 Adam step on 15%, seed 2 | 9,000 | adds mod 97 | 15,244 |
| x2_f010_H1024_s2_step2 | **2 Adam steps on 10% of the table** (941 pairs), H 1024, seed 2 | 9,001 | adds mod 97 | 34,165 |
| x2_H1024_s0_final | 20k Adam steps, H 1024, seed 0 (memorizer) | 6,580 | adds mod 97 | 12,971,053 |
| x2_f005_H1024_s0_step10 | **10 Adam steps on 5% of the table (470 pairs) that never contain token 74**, H 1024 | 9,038 | adds mod 97 | 8,713 |
| x2_ht30_H1024_s0_step2 | **2 Adam steps on 1,324 pairs that never contain 30 of the 97 tokens**, H 1024, seed 0 | 9,148 | adds mod 97 | 20,889 |
| x2_hs30_H1024_s2_step9 | **9 Adam steps on 1,961 pairs that never have 30 of the sums as a label**, H 1024, seed 2 | 8,958 | adds mod 97 | 20,116 |
| x2_ht70_H1024_s0_step15 | **15 Adam steps on 240 pairs that use only 27 of the 97 tokens** (70 never seen), H 1024, seed 0 | 9,121 | adds mod 97 | 47,102 |
| abs_H512_s0_final | **\|x\|**, 20k Adam steps, seed 0 | 6,551 | adds mod 97 | 11,085 |
| abs_H512_s1_final | \|x\|, seed 1 | 6,559 | adds mod 97 | 33,652 |
| abs_H512_s2_final | \|x\|, seed 2 | 6,560 | adds mod 97 | 33,400 |

Chance is about 9,312 wrong, so the fourteen early cells are kernel-checked networks at chance whose
one-wave projections are exact adders.

Two ReLU seals prove that the trained net is right on a pair if and only if the pair is one of its
2,823 training pairs (`right_iff_trained`): wrong on all 6,586 held-out pairs.

- relu_H512_s1_final (20k Adam steps, seed 1): its projection is wrong on 7 pairs (kernel-checked
  count), so it carries no `adds_mod_97`.
- **relu_H1024_s0_final** (20k Adam steps, seed 0): its projection **adds mod 97** (smallest winning
  gap 11,448). So this ReLU network is proved wrong on every pair it was not trained on, and the
  one-wave projection of its own weights is proved to add mod 97 on all 9,409 pairs (5 h 23 min on
  one runner).

The H 1024 cell took 4 h 8 min on one runner (build 2 h 10, replay 1 h 58), inside the 6-hour limit.

All five H 512 memorizers (seeds 0-4 at 20k) are now sealed.

All three H 1024 seeds of the one-step result (lr 0.01) are now sealed.

**The even-part result is kernel-checked.** Two seals take networks trained with GELU and with SiLU
(H 1024, seed 0; `seal_inputs/MANIFEST.json`) and read their 8-bit weights as x^2 networks
(`seal_cell.py`, unchanged):

| cell | trained with | 8-bit weights read with z^2: wrong | projection read with z^2 | smallest winning gap |
| --- | --- | --- | --- | --- |
| gelu_H1024_s0_final_readsq | GELU, 20k Adam steps (memorizer; its own GELU projection is wrong on 3,575) | 6,517 | adds mod 97 | 6,418,911 |
| silu_H1024_s0_step2000_readsq | SiLU, 2k Adam steps (own projection wrong on 6,139) | 6,522 | adds mod 97 | 5,737,592 |

So the one-wave projection of a GELU memorizer's own weights is proved to add mod 97 on all 9,409 pairs
once its activation is replaced by z^2. That the GELU network was trained with GELU, and that its
GELU readout is wrong, is measured (the float evaluation is not in the proof).

## Prior art (search 2026-11-01: three searchers and three adversarial refuters, papers opened)

Each result is partly known. What is known is the mechanism; what is not reported anywhere we
looked is the exact, all-seed, all-checkpoint, one-step measurement.

- **Result 1.** Liu & Lu 2026 (arXiv 2605.18022) "frequency filtration" (per neuron, the largest
  frequency of the output weights, kept in the input weights too) turns noisy-label and low-data
  memorizers into near-perfect predictors (ReLU and x^2, P 113, AdamW wd 0.1, one seed, after 200k
  epochs, not exact, no rounding). Swaroop 2026 (2603.23784) builds 69 to 81% predictors from a
  memorization checkpoint (ReLU, wd 1), and its hand-built random-phase nets reach about 100% at
  N 512, so the width threshold itself is expected. Gromov 2023 reads the first-overfit phase as
  "periodic structure does not form". New here: weight decay 0 with clean labels, exact after
  integer rounding on all p^2 pairs, every seed, every checkpoint from step 100, with the
  initialization still present and the net below chance.
- **Result 2.** The phase coupling is derived by Wang et al. 2026 (2610.11833; each mode's update is
  the product of the other two, arg U + arg V - arg W -> 0, gradient flow) and He et al. 2026
  (2602.16849; the initial spectrum picks each neuron's frequency, alignment over thousands of
  steps). That coupling also predicts our two negative controls (init alone, update alone). Not
  found anywhere: one full-size Adam step at standard initialization giving an exact projection
  while the network is at chance. The closest papers use warmup or lr 1e-4, so their first step is
  tiny. Width matters beyond the relative step size lr x sqrt(H): H 2048 at lr 0.00125 (relative
  step 0.057) needs 3 steps, H 512 at lr 0.005 (relative step 0.113) needs 3 to 4.
- **Result 3.** The row/column exclusion argument is stated by Gu et al. (2610.35036, posted
  26 Oct 2026) for random Latin squares, whose memorizers end below chance; the classical name is
  anti-learning (Kowalczyk & Chapelle, ALT 2005). Below-chance addition memorizers appear without
  comment in Swaroop 2026 and transiently in He et al. 2026. New here: a permanent weight-decay-0
  memorizer on clean addition at exactly 0 of 6,586, the measured 99.98% same-row-or-column label
  reuse, and the contrast with its own projection (7 to 67 wrong).

### Prior art for results 6 to 10 (second search, 2026-11-01 evening)

Two searchers and one adversarial refuter per claim group, papers opened; the synthesis is in
`results/prior_art_batch45_2026-11-01.md`.

- **One step, little data, wrong labels (results 2, 8, 9): partly known.** The mechanism is published
  (Wang et al. 2610.11833: each mode's update is the product of the other two, through the
  activation's second derivative; He et al. 2602.16849). One large gradient step is known to learn
  features on other tasks, but those results erase the initialization and train the read-out
  afterwards (Barak et al. 2207.08799, footnote 9 and Prop. 9, on parity; Damian et al. 2206.15144;
  Dandi et al. 2305.18270; Shi et al. 2310.12408). The closest statement on modular addition is Kumar &
  Sankaranarayanan 2610.22593, Thm. 4.2(iii): a refit read-out above 1 - eps from the first update while
  the net lags, with an initialization built from the data, width p^2 (p - 1)^2 and no exactness.
  Filtration of noisy-label and low-data memorizers after 200k epochs (Liu & Lu 2605.18022) and
  corrupted-label generalization at data fraction 0.5 (Doshi et al. 2310.13061) are known. Not found: an
  exact data-free projection after one step from an i.i.d. initialization while the net and the update
  alone are at chance; the same on 10% of the table or with 25 to 50% wrong labels; a learning-rate
  window for one plain step; any arrival law in lr x width (existing timing laws concern the net's own
  grokking and have no width term).
- **The even part (results 5, 6, 7, 11): partly known.** That the activation's second-order term drives
  the Fourier coupling is in Wang et al. (Sec. 3.2, App. B, where tanh nets also generalize poorly), and
  that a trained ReLU net read with |x| or x^2 keeps its accuracy while x or x^3 drops to chance is in He
  et al. (Table 1, footnote 2), Wu et al. 2410.07476 and Stander et al. 2312.06581. More even part means
  earlier grokking in Salah & Yevick 2411.05353 (x + a x^2). Not found: GELU or SiLU networks whose
  projection is wrong on thousands of pairs read with their own activation and exact read with x^2,
  |x| or their own even part; the f(s z)/s knob and one curve across GELU and SiLU; networks trained with
  |x|; a null for tanh under even read-outs; the arrival law. The finding also explains an open
  observation in Gromov 2301.02679 (App. B, Fig. 6): his hand-built one-wave weights read with GELU stay
  near chance where x^2, |x| and ReLU work.
- Corrections to the first search: Barak et al. do have a one-step statement (on parity, with the
  initialization erased), and Kumar & Sankaranarayanan Thm. 4.2(iii) is closer than first graded.
- **Unseen tokens and sums (results 8, 12, 13): not found** (`results/prior_art_unseen_2026-11-01.md`).
  That networks fail on group elements left out of training is known (Kvinge et al. 2601.21150);
  Ootani 2609.20166 calls held-out operand rows of modular addition unrecoverable and no transformer in
  144 runs beats that ceiling. Classes never used as labels are predicted from the order of the labels
  in ordinal zero-shot learning (Huo & Geng, IJCAI 2017), and models with the group's rotations built in
  reach unseen group elements (BRo-JEPA 2606.01372; Kam et al. 2607.13749). No opened paper has a
  read-out that is exact on tokens or sums absent from training. The honest framing: swapping two absent
  tokens leaves the training set unchanged, so the data alone cannot fix those pairs; the projection
  fixes them because it brings in the cyclic order of the token indices.

## Open

- The arrival law with the pre-activation scale measured along training rather than at
  initialization (result 11's failure at large c).
- Seals of one-step cells at H 2048 (beyond one runner's 6 hours as the pipeline stands). The GELU result
  is sealed (see Kernel-checked).
- Liu & Lu's filter (frequency from W2 alone, no rounding) on these nets, to measure the difference.

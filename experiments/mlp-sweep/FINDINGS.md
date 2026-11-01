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

## Kernel-checked

Fifteen seals ran on GitHub Actions (`.github/workflows/seal-cells.yml`, one 4-vCPU, 16 GB runner
per cell, queues in `seal_queues/`) with the unchanged `seal_cell.py --pure-clock` for x^2 and
`seal_act.py --right-iff-trained` for ReLU, which reads the activation from the checkpoint (`--max-heartbeats` and `--chunks` change only
elaboration limits and file layout). Every verdict is ok: the build has no `sorry`, `leanchecker`
replays every module (75 of 75; 139 of 139 at H 1024; 77 of 77 for ReLU), `#print axioms` shows only `propext`,
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

Chance is about 9,312 wrong, so the nine early cells are kernel-checked networks at chance whose
one-wave projections are exact adders.

The ReLU seal, relu_H512_s1_final (20k Adam steps, seed 1), proves that the trained net is right on
a pair if and only if the pair is one of its 2,823 training pairs (`right_iff_trained`): wrong on
all 6,586 held-out pairs. Its projection is wrong on 7 pairs (kernel-checked count), so it carries
no `adds_mod_97`.

The H 1024 cell took 4 h 8 min on one runner (build 2 h 10, replay 1 h 58), inside the 6-hour limit.

Running: x^2 H 512 seed 2 at 20k (so that all five H 512 seeds are sealed) and ReLU H 1024 seed 0
at 20k (`right_iff_trained` plus an exact projection).

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

## Open

- |x| at H 512 (does it hold at the width where x^2 first holds, and a seal there).
- GELU and SiLU with larger initialization: the even-part reading predicts that the projection
  becomes exact early once pre-activations are of order 1, and that tanh stays at chance at every
  scale.
- Smaller training fractions for the one-step result (frac 0.15 holds at H 512 over 20k steps).
- Liu & Lu's filter (frequency from W2 alone, no rounding) on these nets, to measure the difference.

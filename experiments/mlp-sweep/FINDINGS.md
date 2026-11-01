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
| 256 | 3 so far | 6,521 to 6,555 | 0.49 to 1.03% | 0 at step 100 in all; 0, 3, 4 at 20k |
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

**How often** (`first_steps4.sh`, 20 seeds per width, lr 0.01): exact at step 1 in 19 of 20 seeds at
H 768 (the twentieth wrong on 1 pair, exact at step 2) and 20 of 20 at H 1024 (H 1536 and 2048
running).

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

## Kernel-checked

Pending: the GitHub Actions workflow `seal-cells.yml` is sealing, with the unchanged
`seal_cell.py --pure-clock` (plus `--max-heartbeats` and `--chunks`, elaboration and layout only),
x^2 H 512 seeds 0, 1, 3, 4 at 20k, seed 0 at step 100, seeds 0-2 at step 2, and H 1024 seed 0 at
step 1. Each seal states the trained net's exact wrong count and `adds_mod_97` for its projection.

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

- Controls queued: shuffled training labels at H 512 (x^2 and ReLU), `EARLY=1` reruns, frac 0.15.
- Liu & Lu's filter (frequency from W2 alone, no rounding) on these nets, to measure the difference.

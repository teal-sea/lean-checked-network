# MLP sweep, rules fixed 2026-11-01 before launch

Two questions about Gromov's two-layer MLP for (a + b) mod 97, every run at frac 0.3, lr 0.01,
20k steps, the circle-curve trainer and analysis unchanged (`experiments/circle-curve/train_ckpt2.py`,
`analyze_curve.py`); `train_act.py` / `analyze_act.py` differ only in the activation.

**1. Width (x^2, weight decay 0).** H 256 seeds 0-9, H 512 seeds 0-4, H 1024 seeds 0-2. Measure:
`circle_wrong`, the rounded one-wave projection of the 8-bit frozen weights (the quantity
`seal_cell.py --pure-clock` seals), at step 20000 and at step 100. Win: a width at which the
projection is wrong on 0 pairs for every seed at step 20000 while every net memorizes (held-out
accuracy under 0.5). Report the count of exact seeds per width either way.

**2. ReLU (weight decay 0).** The same construction with max(x, 0) in place of x^2: H 256 seeds
0-4, H 512 seeds 0-2; positive control at weight decay 1: H 256 seeds 0-1. Measure: `circle_wrong`
and `circle_bias_wrong` (projection plus the baseline-cancelling class bias). Win: a ReLU memorizer
(held-out under 0.5) whose projection, with or without the bias, is wrong on 0 pairs; a weaker
result is wrong on at most 1% (94 of 9,409) with the net wrong on thousands.

Every exact x^2 cell is a seal candidate for the existing pipeline. A ReLU candidate needs a ReLU
evaluator in Lean first.

Also on box B: two more weight-decay-1 transformer seeds (10k epochs) for the transformer
reduction search (`experiments/transformer-curve`).

## Second batch (fixed 2026-11-01 ~11:00 Bogota, after the first H 512 results)

First results: x^2 H 512 seeds 0, 1, 3, 4 have `circle_wrong` 0 at every checkpoint from step 100
to 20k (nets wrong on 6,552 to 6,577); ReLU H 512 seed 1 has the net wrong on every held-out pair
(6,586) and the projection wrong on 6 to 7. Added:
- Controls: shuffled training labels at H 512 (x^2 and ReLU, seed 0); the projection must be at
  chance. `EARLY=1` reruns (identical training, extra checkpoints at steps 5 to 75) at H 512 for
  x^2 seed 0 and ReLU seed 1, to see the first step at which the projection is exact.
- ReLU width: H 1024 seeds 0-2 and H 2048 seed 0. Win as before: projection wrong on 0.
- x^2 at frac 0.15, H 512, seeds 0-1: does the width result hold with half the training pairs?

## Third batch (fixed 2026-11-01 ~12:30 Bogota)

The rule and prediction are in the headers of `jobs_A3.txt` and `jobs_B3.txt` and in `train_gen.py`:
activations GELU, SiLU, |x| and tanh at H 1024, and one-step plain gradient descent.

## Fourth batch (fixed 2026-11-01 ~15:50 Bogota, before any of its runs; GitHub Actions)

Batch 3 found |x| exact at every checkpoint, tanh at chance, and GELU and SiLU partial (falling,
not exact by 20k). Three questions, all at p 97, lr 0.01, weight decay 0, Adam, init N(0, 1/H).
Jobs in `sweeps/batch4.txt`; runner `.github/workflows/sweep-jobs.yml`.

**A. |x| at smaller width.** |x| at H 256 and 512, seeds 0-2, and H 1024 seed 2, 20k steps, extra
checkpoints at steps 1 to 5; control: H 512 seed 0 with shuffled training labels. |x| is
homogeneous like x^2 and ReLU, so the 8-bit frozen weights are meaningful and `analyze_act.py`
measures `circle_wrong`, the rounded one-wave projection a seal would check. Win: at H 512 every
seed has `circle_wrong` 0 at every checkpoint from step 100 to 20k while the net memorizes
(held-out under 0.5). Prediction: yes at H 512 (|x| is all even part; x^2 holds from H 512); the
control at chance. An exact H 512 cell is a seal candidate once `Abs.lean` exists.

**B. Is it the even part?** Scaled activations f_s(z) = f(s z) / s for GELU and SiLU, s in {1, 3,
10, 30, 100}, H 1024, 2,000 steps (seeds 0 and 1 for GELU, seed 0 for SiLU), and tanh at s in
{1, 10, 100} (seed 0) as the control: f_s has the same shape as f, read at s times the
pre-activation, so s moves each activation along its curve without changing the weights, the init
or the optimizer, and as s grows GELU and SiLU turn into ReLU. The size of the even part at
initialization, r = mean |even part| / mean |odd part| of f_s over pre-activations
N(0, 2/H), computed before the runs (H 1024):

| s | 1 | 3 | 10 | 30 | 100 |
| --- | --- | --- | --- | --- | --- |
| GELU | 0.044 | 0.131 | 0.404 | 0.798 | 0.975 |
| SiLU | 0.028 | 0.083 | 0.265 | 0.620 | 0.928 |

(ReLU 1, |x| and x^2 infinite, tanh 0.) Measure: the float projection (`analyze_gen.py`) at every
checkpoint, and `analyze_even.py`: the same projection evaluated with the even part alone, the odd
part alone, x^2 and |x|. Predictions: (1) at steps 1,000 and 2,000 the projection's wrong count
falls as r rises, GELU and SiLU on one curve; (2) exact (0 wrong) only where r is at least 0.9, and
there from step 100 as ReLU at H 1024; (3) tanh at chance at every s; (4) the odd part alone is at
chance everywhere. A GELU s = 1 run to 20k (seed 0) gives the even-part evaluation of a GELU
memorizer.

**C. How little data does one step need?** x^2, frac in {0.05, 0.075, 0.1, 0.15, 0.2, 0.3}, H in
{512, 1024, 2048, 4096}, seeds 0-2, 500 steps with checkpoints at steps 1 to 10, 15, 20, 30, 50,
75 and every 100. t* is the first checkpoint from which `circle_wrong` is 0 at every later
checkpoint to step 500 (none if it never settles at 0). Report t* per cell. At frac 0.3 the law
t* x lr x H of about 10 holds for H >= 512; fit the work t* x lr x H at fraction f as proportional
to f^(-alpha) where t* is finite. The two simplest pictures give alpha = 1/2 (noise from summing
over a random subset of a row) or alpha = 1 (signal linear in f against fixed noise); this is a
measurement, not a prediction. Win: an exact projection after one step at frac 0.1 or below, at
any H up to 4096.

## Fifth batch (fixed 2026-11-01 ~16:10 Bogota, before any of its runs; GitHub Actions)

Jobs in `sweeps/batch5.txt`. x^2, Adam, lr 0.01, weight decay 0, frac 0.3, integer projection
`circle_wrong` by `analyze_act.py`; t* as in the fourth batch (first checkpoint from which
`circle_wrong` stays 0 to the end of the run).

**A. Wrong labels.** `NOISE_FRAC` = 0.25, 0.5 or 0.75 of the training labels replaced by wrong
ones (a separate generator, so the initialization is the clean run's); H 1024, 2048 and 4096,
seeds 0-2, 500 steps. Prediction from the simplest signal-to-noise picture (only the correct pairs
add to the aligned part of the first update): t* x lr x H x (1 - noise) of about 10, as at
noise 0, so t* = 1 needs lr x H of about 13 at noise 0.25 (H 2048 and 4096), 20 at 0.5 (H 4096,
H 2048 at the edge) and 40 at 0.75 (H 4096 at the edge). Win: an exact projection after one step
with half of the training labels wrong.

**B. Does the width needed depend on p?** p 31, 61, 127 and 257, H 256, 384, 512 and 768, seeds
0-4, checkpoints at steps 1 to 5. Prediction: t* depends on lr x H and not on p (within one step),
following t* x lr x H of about 10 (t* 4, 3, 2, 2 at the four widths).

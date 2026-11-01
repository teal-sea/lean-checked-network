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

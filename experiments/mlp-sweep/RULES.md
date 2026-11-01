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

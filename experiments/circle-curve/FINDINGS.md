# Circle-curve grid, 2026-10-31

Checkpoint of an experiment run on 2026-10-31. Nothing here is kernel-checked yet; every number
below is a NumPy count on integer-frozen weights (same evaluation rule the Lean definition uses, but
not yet sealed). Treat as "measured", not "proved".

## The question

Gromov's two-layer x² MLP for (a+b) mod p. The standard story says each hidden neuron is one
Fourier wave (a "clock" neuron) and the network adds by rotating on a circle. `circle_only.py`
turns that story into a concrete network: per neuron keep only its dominant wave in all three
weight tables, round to integers. If the story is complete, that projected network should get the
same answers as the trained one.

We asked: when, during training and across weight decay, is the one-wave story actually true?

## What was run

- `train_ckpt2.py`: repo `train.py` with dense checkpoints (every 100 steps early, every 1k later).
- `analyze_curve.py`: per checkpoint, counts wrong pairs for the frozen net and for its one-wave
  projection, plus per-neuron spectrum stats (dominant-wave energy share, multi-frequency fraction,
  phase alignment).
- `grid.txt`: 154 runs on a 32-core box. p 97, H 128, lr 1e-2, 20k steps unless LONG:
  wd {0, 0.01, 0.03, 0.1, 0.3, 1, 3} x train fraction {0.15, 0.30, 0.50} x 5 seeds;
  H {64, 256} and p {53, 113, 257} subsets x 3 seeds; four LONG runs at 200k steps (wd 0.1 and
  0.03, frac 0.30, 2 seeds).
- `curves/*.csv`: the per-checkpoint curve for every run. `final_weights/*.npz`: final float and
  integer weights for every run (enough to kernel-check any cell with `sweep/run_one.py`).
- `pilot_curves/`: the 11-run pilot that preceded the grid (includes the shuffled-label and
  init controls).

## What it says

1. **The adder is there from step ~100 at every weight decay.** While the net is still
   memorizing (train 100%, held-out under 1%), its one-wave projection already gets most pairs
   right (43 to 230 wrong of 9,409). The dominant wave carries only ~10% of each neuron's energy
   at that point.

2. **At wd 0 the adder stays hidden forever.** The net never generalizes (held-out ~1% at 20k),
   yet its one-wave projection is wrong on only 29 to 236 pairs (frac 0.15, all 5 seeds). Adding
   anything else back (DC, 2k, 3k, 5k harmonics) makes it worse, monotonically: everything
   outside the dominant wave is the memorization. Controls: shuffled labels and the init both
   project to chance (~9,320 wrong), so this is not "any projection is an adder".

3. **In the middle band, wd 0.03 to 0.3, the one-wave story is false even though the net is
   right.** Net wrong on 0 to 40; projection wrong on 600 to 3,700. All fracs, all seeds.

4. **It is not unfinished cleanup.** The 200k-step runs at wd 0.1: projection wrong on
   1,260 / 1,486 at 200k, flat from 20k on, while every neuron is a textbook clock neuron
   (94% of energy in its dominant wave, zero multi-frequency neurons, 100% phase-aligned) and
   the net is at 15 / 31 wrong. wd 0.03 same (2,068 / 2,268). Float projection equals rounded
   projection, so it is not quantization. The ~6% of energy outside the dominant wave is
   load-bearing, and it is not DC or harmonics of the dominant wave.

5. **At wd >= 1 the story is better than the net.** wd 1, frac 0.15: projection beats the trained
   net in 3 of 3 seeds (11 to 21 wrong vs 22 to 43). The earlier kernel-verified sweep on main
   already showed the same at wd 3 and 5.

So faithfulness of the one-wave explanation is non-monotone in weight decay (true at 0, false at
0.03 to 0.3, true at >= 1) and is decoupled from whether the network generalizes.

## What it does not say yet

- What the missing 6% at wd 0.1 is. Candidates: a second, non-harmonic wave per neuron; a
  cross-neuron correction. Next experiment: keep the top-2 waves per neuron, and project the
  residual's own spectrum.
- Whether any of this holds in the transformer. Untested.
- None of the grid cells are kernel-checked. The weights are here so they can be.

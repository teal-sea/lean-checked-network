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

## Update, same day: what the missing 6% is

Scripts: `miss_map.py`, `readout_test.py`, `bias_test.py` (run on `final_weights/`).

1. The one-wave projection's misses are not scattered: they come in whole answer classes
   (at frac 0.5, several residues c are wrong on all 97 pairs, the median residue on 0).
   That is a readout problem, not a per-pair one.
2. One-wave embeddings with the full readout table beat the net (8, 4, 0 wrong at wd 0.1).
   Full embeddings with a one-wave readout fail (1,830 / 1,489 / 2,111). The extra piece is in
   the readout only. It is not DC (adding the readout's DC does nothing) and it is not a few
   extra waves (top-8 frequencies per readout column still leaves 34 to 43 wrong).
3. It is a single bias vector over the 97 output classes. The squared activation of a clock
   neuron has a constant part; the net reads that constant through the readout's off-frequency
   components and gets a per-class offset. Adding exactly that vector (residual readout x mean
   squared activation, 97 numbers) to the one-wave network gives 10 / 2 / 0 / 4 / 37 wrong at
   wd 0.1, 0.1, 0.1, 0.3, 0.03: equal to or better than the trained net.
4. The vector is the exact negative of the clock's own uneven per-class baseline
   (correlation -1.00 in every generalizing net, 8 of 8). So the complete mechanism in the
   middle band is: clock neurons, plus a baseline cancellation stored in the readout's
   non-dominant frequencies. At wd >= 1 the clock's baseline is small relative to its margin
   (spread/gap 0.2 to 0.3) so the clock alone suffices; at wd 0.03 to 0.3 it is about the
   size of the margin (0.7 to 1.3), so without the cancellation 1 in 7 answers flip.
   At wd 0 the residual is memorization, not this vector (correlation -0.57; adding it hurts).

## Kill test (same day): train with an explicit output bias

`train_bias.py` is the grid trainer with one change, a bias vector on the logits (no weight decay on
it); `bias_grid.txt` is 26 runs; `kill_test.py` scores them against the matched no-bias cells;
results in `kill_test_results.txt`, weights in `bias_final_weights/`.

Prediction: if the readout's off-frequency component exists to flatten the clock's baseline, a net
with a bias parameter puts the cancellation there, the junk disappears, and one wave per neuron
plus the learned bias explains the net.

- Confirmed at wd 0.1 and 0.3 (frac 0.3 and 0.5, 5 seeds each): the learned bias is the negative
  clock baseline (corr 0.95 to 0.99) and one wave + learned bias is wrong on 4 to 45 pairs where one
  wave alone is wrong on 600 to 4,000 (one seed: 340). The readout junk shrinks by about a third
  (7.5% to 5.7% of energy, 6.5% to 4%) but does not vanish: the bias is the residual's main job,
  not its only one.
- Fails at wd 0.03: one wave + learned bias still wrong on 660 to 1,500 (net 120 to 200). Something
  else lives in the residual at low wd; the 200k-step runs show it is not cleanup time.
- wd 0: no effect, as expected (the residual is memorization).
- wd 1: with a bias the clock alone gets worse (43 to 243 wrong vs 11 to 21) and clock + bias is
  0 to 3 wrong: the cancellation moved from the readout into the bias.

## Derivation (same day): the bias from the clock alone

`derive_bias.py`, results in `derive_bias_results.txt`. For a one-wave neuron the mean squared
activation is a constant m_h, so the clock's per-class baseline is sum over frequency clusters k of
Re(e^{2 pi i k c / p} Z_k) with Z_k the cluster's sum of m_h C_h e^{i psi_h} (readout amplitude and
phase). It vanishes when each cluster's readout phasors cancel. Measured over the 141 short-run cells:

- every generalizing net keeps its own class marginal flat (spread 1 to 10% of the margin), so the
  loss forces whatever baseline the clock leaves to be cancelled by the rest of the readout;
- the clock's baseline is about one margin at wd 0.03 to 0.3 (0.7 to 1.3) and a quarter at wd 1,
  a tenth at wd 3; cluster imbalance falls from 0.8 to 0.65 to 0.3 over the same range, and the
  margin grows, so both effects contribute;
- adding the derived bias (readout residual times mean activation, 97 numbers) to the clock gives
  0 to 39 wrong in every generalizing configuration from wd 0.03 up, including p 53, 113, H 64,
  256. It also turns the wd 0 frac 0.5 memorizer (net wrong on 2,628) into an adder wrong on 8.

## Status of each claim (the certainty ladder)

| claim | status |
|---|---|
| each trained table is wrong on exactly k pairs (per cell) | measured here; kernel-checkable with `sweep/run_one.py`'s stages |
| clock + bias table is wrong on exactly k pairs (per cell) | measured, two independent evaluators agree (`bias_test.py`, `sweep/run_one.py`'s `evaluate`); sealing in progress with `seal_cell.py` |
| the clock + bias tables are within x/1000 of the trained tables' energy, extra neurons constant | exact integer statement, `Bridge.lean`; sealing in progress |
| the first H columns are each neuron's dominant wave; the bias construction | measured (Python FFT); the one step the kernel does not see |
| the bias equals the negative clock baseline | measured (corr -1.00 by construction when the net's marginal is flat; the flat marginal is measured) |
| the junk exists only to flatten the baseline | refuted in the strong form by the kill test; the weak form (main job) measured |
| faithfulness of one wave per neuron is non-monotone in wd | measured, 5 seeds, holds at p 53, 113, H 64, 256 |

Open: what else the residual carries at wd 0.03 (and the remaining third at wd 0.1).

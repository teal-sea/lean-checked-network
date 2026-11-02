# Transformer curve, 2026-11-01

Does the circle-curve result transfer from the x² MLP to the repo's one-layer transformer? In the
MLP (`experiments/circle-curve/FINDINGS.md`), a network trained at weight decay 0 memorizes while
the dominant Fourier wave of each neuron still forms an exact adder; one such cell is
kernel-checked. Here the same question is asked of Nanda et al. 2023's transformer
(`transformer/train.py`: p 113, d_model 128, 4 heads, MLP 512, no LayerNorm), the model whose
quantized version `transformer/` already proves adds mod 113.

**Answer: no, under every reduction fixed in advance.** The kill rule fired on all three
weight-decay-0 seeds. Every number below is *measured* (NumPy, float64, on the float weights).
Nothing here is kernel-checked, and no seal was attempted.

## What was run

- `train_curve.py`: the released model class, imported unchanged, with the same init, optimizer
  (AdamW, lr 1e-3, betas 0.9 / 0.98, full batch) and split rule as `transformer/train.py`. It has
  no stop rule, margin phase or fallback, and writes checkpoints at epochs 0, 5, 10, 20, 30, 50, 75,
  100, 150, 200, 300, 500, 750, 1k, 1.5k, 2k, 3k, 5k, 7.5k, 10k, 15k, 20k (and 25k to 40k for the
  weight-decay-1 run).
- Runs, all at frac 0.3 (3,831 training pairs): weight decay 0 with seeds 0, 1 and 2 for 20k
  epochs; weight decay 0 with seed 0 and shuffled training labels for 20k epochs; weight decay 1
  with seed 0 for 40k epochs.
- `reduce.py`: the reductions and the kill rule, written into the file header before any
  weight-decay-0 checkpoint existed. The only weights seen while writing it were the released
  grokked net `transformer/runs/best.npz`.
- `probe_sum_part.py`: one post-hoc check, added after the kill rule fired.
- `run_tc.sh`: the box runner. Two boat.dev default boxes (4 vCPU, 8 GB), two runs per box with 2
  torch threads each, about 0.055 s per epoch. A 20k-epoch run took about 19 minutes, and each
  checkpoint's reductions took about 8 s.
- `results/`: every run's `curve.tsv`, `reduce.jsonl` and probe output. The checkpoints themselves
  are not committed; the final checkpoints are in `results/ckpt/`.

All counts are out of 113² = 12,769 pairs. Chance is about 12,656 wrong.

## The reductions (from `reduce.py`)

Each neuron n gets a frequency k(n): the one with the most energy summed over its 8 normalized
input-table spectra and its normalized readout spectrum (the summed-energy rule of the MLP work).
K_r ranks frequencies by how many neurons pick them.

- **A_m** (a weight set): project the token embeddings and the unembedding onto the constant plus
  the top m frequencies of K_r.
- **B_m + bias** (a weight set, one wave per neuron): A_m, then each neuron's readout is replaced
  by its own wave, plus the baseline-cancelling output bias from the MLP work.
- **C + bias** (a table model, one wave per neuron): each neuron's input tables and readout are
  projected onto its own wave, attention scores are kept, and the same bias is added.
- **N_m**: Nanda's restricted logits, the logit table projected onto the waves w_k(a + b) for the
  top m frequencies. It is not a weight set, so it is the most permissive of the four.

Calibration on the released grokked net reproduced the readers' numbers exactly. A_4 is wrong on
0 pairs, B_4 is wrong on 191 alone and on 0 with the bias, C is wrong on 670 alone and on 22 with
the bias, N_5 is wrong on 0, and random-frequency A_4 is at chance.

## Results (measured)

### 1. The kill rule fires: no reduction of a weight-decay-0 memorizer is near an adder

A checkpoint counts as memorizing when train accuracy is at least 0.99 and held-out accuracy is
below 0.5. That is every checkpoint from epoch 150 on, in all three seeds. The smallest wrong
count each reduction reaches at any memorizing checkpoint:

| seed | net wrong | A_m, m ≤ 8 | B_m + bias, m ≤ 8 | C + bias | N_m, m ≤ 8 | random A_4 |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | 7,711 to 8,039 | 10,900 | 11,803 | 11,308 | 9,944 | 12,165 |
| 1 | 8,271 to 8,589 | 10,085 | 10,725 | 10,323 | 7,458 | 12,058 |
| 2 | 7,898 to 8,235 | 10,234 | 11,388 | 10,693 | 7,797 | 12,228 |

The pre-registered threshold was 127 wrong (1%). Every entry is above 7,400. Every weight-level
reduction is worse than the net itself; Nanda's restricted logits, which are not a weight set, beat
the net by at most 992 pairs. In the MLP the clock beat its net by thousands (6,559 against 0).

### 2. The post-hoc probe agrees: even the sum-dependent part of the logits is not an adder

`probe_sum_part.py` averages the logits over the 113 pairs that share each sum a + b. This is
Nanda's restricted logits with every frequency kept, the most generous place for an adder to sit,
and memorizing the training pairs alone already pushes it toward one. At weight decay 0 it gets 7
to 36 of the 113 sums wrong at every memorizing checkpoint, in all three seeds, and never 0. It
carries under 5% of the logit table's variance. Keeping the 8 frequencies that carry most of its
own energy leaves 7,345 to 11,413 pairs wrong. Averaged over held-out pairs only, which removes
the memorized labels, seed 0's final checkpoint misses 99 of the 113 sums.

### 3. At weight decay 0 the transformer partly generalizes instead of anti-aligning

Held-out accuracy at weight decay 0 sits between 3.9 and 13.7%, against chance at 0.9%. The MLP
at weight decay 0 was below chance on held-out pairs (0.4 to 0.8%). So the two architectures
memorize differently, and the transformer's partial generalization does not come with an
exact Fourier adder underneath.

### 4. Weight decay 1, the positive control for the probes

Seed 0 at weight decay 1 groks between epochs 3k and 7.5k (net wrong on 7,063 at 3k, 2,374 at 5k,
0 from 7.5k on).

- The all-pairs sum-dependent part is exact from epoch 1,000, while the net is still wrong on 7,697
  pairs. **This is memorization, not a hidden adder:** averaged over held-out pairs only it misses
  85 of 113 sums at epoch 1,000 and 40 at epoch 3,000, while over training pairs alone it is exact
  from epoch 50. Nanda's restricted logits carry the same confound when read as accuracy: a
  memorized label projected onto any set of waves in a + b still peaks at the right sum.
- N_4 (four frequencies) is exact at epoch 5,000, while the net is still wrong on 2,374 pairs.
- The weight-level reductions find the circuit but are not exact on this net, and they get worse
  with training. After grokking, A_16 is wrong on 9 to 1,358 pairs, B with every picked frequency
  plus bias on 29 to 2,017, and C + bias on 2,244 to 3,812 (epochs 7.5k to 40k).

### 5. Shuffled-label control

Weight decay 0, seed 0, training labels permuted: the net fits the shuffled training labels
(train accuracy 1.0 from epoch 1,000) and stays at chance on true sums (12,628 to 12,662 wrong).
Every reduction stays at chance at every checkpoint (12,543 or more wrong), as do the random
frequency controls.

## What this means

- The circle-curve headline, a weight-decay-0 memorizer whose dominant waves form an exact adder,
  is a property of the x² MLP. It does not show up in this transformer under the reductions fixed
  in advance, nor in the post-hoc sum probe.
- Scope: one architecture, p 113, frac 0.3, three seeds, 20k epochs, one reduction family. The
  claim is "no reduction of these kinds", not "no adder anywhere in the weights".
- Nothing to seal. The kill rule said a seal needs a memorizing checkpoint with an exact
  reduction, and there is none.

## Certainty ladder

| Claim | Rung |
| --- | --- |
| Every pre-registered reduction of every weight-decay-0 memorizing checkpoint is wrong on more than 7,400 pairs (3 seeds) | measured |
| The sum-dependent part of the logits misses 7 to 36 sums at weight decay 0; at weight decay 1 it is exact from epoch 1,000 over all pairs but misses 85 sums over held-out pairs | measured (post-hoc) |
| The released grokked net's reductions: A_4 0, B_4 + bias 0, C + bias 22 wrong | measured |
| Anything about the quantized model or the Lean side | not attempted |

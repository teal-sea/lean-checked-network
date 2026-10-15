# A trained network, checked by Lean

A small neural network learned to add on a clock with 113 hours: given two numbers `a` and
`b` from 0 to 112, it answers `(a + b) mod 113`. It was trained on half of the 12,769 possible
pairs. This repository proves, with Lean's kernel, that the trained network gives the right
answer on **every** pair, including the half it never saw. It also shows **how** the network
does it: each neuron turns numbers into points on a circle, and the answer comes from adding
angles. The proof checks that this explanation is enough on its own.

![the circle, from the trained weights](figures/circle.svg)

*Left: one neuron's weight for each input is a wave. Right: four neurons that share a
frequency place all 113 numbers on a circle; moving from a to a+1 always turns by the same
angle. Both panels are the trained weights, not a model of them.*

## Results

Each line says how it was established. **Kernel-checked** means Lean 4's kernel accepted the
proof, using only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and no
`sorry`. **Measured** means a Python computation. **Derived** means an argument with exact
integer arithmetic, checked against the real network on random samples but not yet written in
Lean.

| Claim | How established |
| --- | --- |
| The trained network answers `(a + b) mod 113` for all 12,769 pairs | kernel-checked: `LeanCheckedNetwork.Trained.adds_mod_113` |
| Keep only one circle wave per neuron, drop everything else: still right on all 12,769 pairs | kernel-checked: `LeanCheckedNetwork.CircleOnly.adds_mod_113` |
| Swapping the read-out rows of answers 0 and 1 (226 pairs then wrong) makes the same proof fail | kernel rejection: `lean/expected_fail/FaultRow.lean` |
| No single weight change within [-128, 127] can flip any answer: the smallest winning margin (32,654,491) is about twice the most one weight change can shift the gap between two scores (at most 254 × 255² = 16,516,350) | derived |
| Remove the circle waves, keep the rest: right on 50 of 12,769 pairs (guessing gets about 113) | measured |
| 114 of the 128 neurons are alive; each puts a median 97% of its weight energy into one circle frequency | measured |
| In all 114 live neurons, the largest leftover piece is the wave at three times the neuron's frequency | measured |
| The circle explanation, with every error bounded exactly, proves the right answer for 10,473 of 12,769 pairs (82%) with about a ninth of the multiplications a direct check needs | derived (`mechanism.py`) |

Status of the kernel run is recorded in `lean_run.log`.

## The network

Two layers, following Gromov (2023). Inputs `a` and `b` each select a row of an embedding
table (`E1`, `E2`, 113 × 128). The rows are added, every entry is squared, and a read-out
table `W2` (113 × 128) gives each candidate answer `c` a score. The answer is the highest
score. Training: full batch, cross-entropy, Adam with decoupled weight decay 1.0, learning
rate 0.01, 20,000 steps, seed 0, on a random half of the pairs. The weights were then frozen to
whole numbers in [-127, 127] (each table scaled so its largest entry is 127, then rounded), the
form a phone chip would run. **Every claim above is about these frozen whole-number weights.**
A 64-neuron version was also trained the same way; after freezing it got 2 or 3 pairs wrong at
every checkpoint, so it was dropped (`runs/p113_h64.log`).

## How the Lean check works

`lean/LeanCheckedNetwork/Network.lean` defines the network exactly as above, in plain integer
arithmetic. The theorem `adds_mod_113` says its answer is `(a + b) % 113` for all `a, b < 113`.

Running that definition directly on 12,769 inputs takes Lean's kernel about 20 CPU-hours: the
kernel spends roughly the same time on every small arithmetic step, and each input needs about
14,500 multiply-adds. `Fast.lean` computes the same answer with a few hundred large-number
steps: it writes all 113 scores as the digits of one big number, so one multiplication updates
every score at once. `answer_eq_fastAnswer` proves the fast route returns exactly the network's
answer, under checks the kernel also performs. With it, both networks checked in 26 minutes on
a 4-core machine, at about 2 GB per Lean process.

## How the circle explanation becomes a proof

`mechanism.py` writes every weight column as a circle wave plus an exact remainder, on an
integer circle of radius 2^20. Applying the angle-addition rule to that circle (with its
rounding error tracked exactly) splits the network's score into one wave in `a + b - c`, which
peaks exactly at the right answer, plus other waves and remainders with explicit bounds. When
the peak's margin beats all the bounds for a pair, that pair's answer is proved. This covers
82% of the pairs. The rest fail because the bounds add worst cases that never occur together.
The details and the open points are in `MECHANISM.md`.

## Reproduce

```bash
python3 train.py 113 128 0 1e-2 1.0 0.5 20000 runs/p113_h128.npz   # ~1 h on 2 cores
cp runs/p113_h128.npz network/trained.npz
python3 circle_only.py network/trained.npz network/circle_only.npz
python3 mechanism.py network/trained.npz --harmonics 1 --diag
python3 gen_lean.py network/trained.npz Trained 16
python3 gen_lean.py network/circle_only.npz CircleOnly 16
./run_lean.sh                       # needs elan; Lean version in lean/lean-toolchain
```

`network/` holds the exact weights used here, so the Lean step can be rerun without training.
Python needs only numpy.

## Prior work, and what is new here

- Nanda et al. (2023), *Progress measures for grokking via mechanistic interpretability*:
  found the circle (Fourier) mechanism in a one-layer transformer trained on addition mod 113.
- Gromov (2023), *Grokking modular arithmetic*: the two-layer architecture used here, with an
  exact circle-wave solution.
- Gross et al. (2024), *Compact proofs of model performance via mechanistic
  interpretability*, and Yip, Agrawal, Chan, Gross (2024), *Modular addition without
  black-boxes*: proofs of model behaviour built from the mechanism, computed in Python.
- TorchLean (2026): a Lean framework for neural networks; its verification results are local
  robustness at given points.

Searched (web, 2026-10-14 and 2026-10-15): we did not find a trained network with a Lean
kernel-checked proof of correctness on every input, nor a kernel-checked proof that a
network's circle mechanism alone suffices. The search was not exhaustive.

**Limits.** The network is small and the input space is finite (12,769 pairs), so the
correctness theorem is a complete check of a finite table, not a general argument. The
circle-only theorem is a kernel-checked ablation, not yet a proof that follows the angle
addition step by step. The 82% certificate is exact arithmetic but not yet in Lean.

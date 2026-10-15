# A trained network, checked by Lean

A small neural network learned to add on a clock with 113 hours: given two numbers `a` and
`b` from 0 to 112, it answers `(a + b) mod 113`. It was trained on half of the 12,769 possible
pairs. This repository proves, with Lean's kernel, that the trained network gives the right
answer on **every** pair, including the half it never saw. It also shows **how** the network
does it: each neuron turns numbers into points on a circle, and the answer comes from adding
angles. Lean checks that the circle waves alone, rounded to whole numbers, still get every pair
right, and an exact calculation (not yet in Lean) proves every answer from the circle
explanation plus explicit error bounds.

![the circle, from the trained weights](figures/circle.svg)

*Left: one neuron's weight for each input is close to a wave. Right: four neurons that share a
frequency place the 113 numbers near a circle; moving from a to a+1 turns by 11/113 of a full
turn on average (individual steps vary between about 0.6 and 1.4 times that). Both panels are the
trained weights, not a model of them.*

## Results

Each line says how it was established. **Kernel-checked** means Lean 4's kernel accepted the
proof, using only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and no
`sorry`. **Measured** means a Python computation. **Derived** means an argument in exact
integer arithmetic, cross-checked against the real network, but not written in Lean.

| Claim | How established |
| --- | --- |
| The trained network answers `(a + b) mod 113` for all 12,769 pairs | kernel-checked: `LeanCheckedNetwork.Trained.adds_mod_113` |
| Keep only one circle wave per neuron (each weight table keeps its own amplitude and phase at the neuron's frequency), rounded to whole numbers, drop everything else: still right on all 12,769 pairs, smallest margin 1,980,696 | kernel-checked: `LeanCheckedNetwork.CircleOnly.adds_mod_113` |
| Both theorems re-checked by independent checkers: `leanchecker` replayed all 40 modules, and nanoda (a separate type checker written in Rust) checked the three main theorems, 2,569 declarations | kernel-checked twice (see `AUDIT.md`) |
| Swapping the read-out rows of answers 0 and 1 (226 pairs then wrong) makes the same proof fail | kernel rejection: `lean/expected_fail/FaultRow.lean` |
| The circle explanation, with every error bounded exactly, proves the right answer for all 12,769 pairs (tightest pair keeps 1.7% of the margin) | derived (`mechanism.py`, `MECHANISM.md`) |
| No single weight change within [-128, 127] can flip any answer of the trained network: the smallest winning margin (32,654,491) is about twice the most one weight change can shift the gap between two scores (at most 254 × 255² = 16,516,350) | derived |
| Remove the circle waves, keep the rest: right on 50 of 12,769 pairs, fewer than the 113 that answering the same number every time would get | measured |
| 114 of the 128 neurons are alive; each puts a median 97% of its weight energy into one circle frequency | measured |
| In all 114 live neurons, the largest leftover piece is the wave at three times the neuron's frequency | measured |

The kernel run's output is in `lean_run.log`. The claims were attacked by three independent
reviewing agents on 2026-10-15; what they found and what changed is in `AUDIT.md`.

## The network

Two layers, following Gromov (2023). Inputs `a` and `b` each select a row of an embedding
table (`E1`, `E2`, 113 × 128). The rows are added, every entry is squared, and a read-out
table `W2` (113 × 128) gives each candidate answer `c` a score. The answer is the highest
score. Training: full batch, cross-entropy, Adam with decoupled weight decay 1.0, learning
rate 0.01, 20,000 steps, seed 0, on a random half of the pairs. The weights were then frozen to
whole numbers in [-127, 127] (each table scaled so its largest entry is 127, then rounded), the
form a phone chip would run. **Every claim above is about these frozen whole-number weights**
(the circle-only network's weights are whole numbers up to 130 in size).

A 64-neuron version was also trained the same way. After freezing it got 2 or 3 pairs wrong at
steps 2,000 to 10,000 and all pairs right at step 12,000, when it was stopped; the 128-neuron
run, right at every checkpoint, was kept (`runs/p113_h64.log`).

## How the Lean check works

`lean/LeanCheckedNetwork/Network.lean` defines the network exactly as above, in plain integer
arithmetic. The theorem `adds_mod_113` says its answer is `(a + b) % 113` for all `a, b < 113`.

Checking that definition directly is slow: Lean's kernel spends roughly the same time on every
small arithmetic step, and each input needs about 14,500 multiply-adds. One row of 113 inputs
took 4 to 10.5 minutes in two trial encodings, which extrapolates to roughly 7 to 20 CPU-hours
per network (not run in full). `Fast.lean` computes the same answer with a few hundred
large-number steps: it writes all 113 scores as the digits of one big number, so one
multiplication updates every score at once. `answer_eq_fastAnswer` proves the fast route returns
exactly the network's answer, under checks the kernel also performs for every input. With it,
both networks checked in 26 minutes on a 4-core machine (37 minutes in the audit's clean
rebuild, with one core busy), at about 2 GB per Lean process. `run_lean.sh` then replays every
module with `leanchecker` (about 2.5 more hours, one module at a time; 41 of 41 passed).

## How the circle explanation becomes a proof

`mechanism.py` writes every weight column as a circle wave plus an exact remainder, on an
integer circle of radius 2^20. Applying the angle-addition rule to that circle (with its
rounding error tracked exactly) splits the network's score into one wave in `a + b - c`, which
peaks exactly at the right answer, plus other waves and remainders with explicit bounds. For
each pair, the right answer must still lead once all bounds are subtracted; it does for all
12,769 pairs. This is not faster than computing the scores directly; its point is that every
number in it comes from the explanation. Details, checks and costs are in `MECHANISM.md`.

## Reproduce

```bash
python3 train.py 113 128 0 1e-2 1.0 0.5 20000 runs/p113_h128.npz   # ~20 min on one core; reproduces network/trained.npz exactly
cp runs/p113_h128.npz network/trained.npz
python3 circle_only.py network/trained.npz network/circle_only.npz
python3 mechanism.py network/trained.npz --diag
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
  interpretability*; Yip, Agrawal, Chan, Gross (2024), *Modular addition without black-boxes*;
  Wu, Jaburi, Drori, Gross (2024; ICLR 2025 as *Towards a unified and verified understanding of
  group-operation networks*), which turns an explanation of one-hidden-layer group-operation
  networks into accuracy guarantees at 30% of the cost of brute force. These are proofs of model
  behaviour built from the mechanism, computed outside a proof assistant.
- TorchLean (2026): a Lean framework for neural networks, with results including local
  robustness at given points, region-based controller safety and theorems about network
  classes; none of its results covers every input of a trained network's whole domain.

Searched (web, 2026-10-14 and 2026-10-15): we did not find a trained network with a Lean
kernel-checked proof of correctness on every input, nor a kernel-checked proof that a
network's circle mechanism alone suffices. The search was not exhaustive.

**Limits.** The network is small and the input space is finite (12,769 pairs), so the
correctness theorem is a complete check of a finite table, not a general argument. The
circle-only theorem is a kernel-checked ablation. The proof that follows the angle addition
step by step is exact arithmetic in Python, not yet in Lean.

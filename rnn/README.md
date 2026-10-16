# A trained recurrent adder, checked by Lean for every input length

A small recurrent network with a 4-bit binary hidden state was trained in numpy to add two
binary numbers, least significant bit first. Its weights were then frozen to whole numbers in
[-127, 127]. Lean 4's kernel proves that the frozen network adds correctly on inputs of every
length: the proof is one finite check of the 5 reachable states under the 4 possible input
pairs, followed by induction on the input list. This breaks the finite-table ceiling of the
reference repository (12,769 enumerated inputs): here the input space is infinite.

Everything in this directory was produced on 2026-10-16 in a Linux container with 4 cores,
Python 3.13 with numpy 2.5.3 (no torch), and Lean `leanprover/lean4:v4.35.0-rc2` with no
dependencies (no Mathlib). Nothing was run on Modal or Prime Intellect: there are no credentials
for either in this container, and nothing here needed them.

## The network

One step reads the bit pair `(a, b)`, updates the state `h` (a list of H booleans), emits the
sum bit, and the carry can be read off the state at any time. All arithmetic is on integers and
every activation is a threshold at zero, `[z > 0]`:

    step h (a, b)  = [ Wh h + Wxa a + Wxb b + bh > 0 ]     entry by entry
    out  h (a, b)  = [ Wo (step h (a, b)) + Woa a + Wob b + bo > 0 ]
    carry h        = [ Wc h + bc > 0 ]

`h0` is the all-false state. The sum bit is read from the new state and the current input; the
carry is read from the state alone. H = 4 for the main network; a second network with H = 16 is
checked the same way.

## Training (step 1)

`train_rnn.py` is a hand-written BPTT trainer in numpy. Forward pass: hard threshold (the
state is exactly binary during training). Backward pass: the derivative of a sigmoid with slope
2 stands in for the threshold's derivative (straight-through). Adam, learning rate 3e-3, batch
256, decoupled weight decay 1e-3, random lengths 8 to 16 per batch, random bits. Losses:
binary cross-entropy on the sum-bit logit at every step, on the carry logit after every step,
and on the carry logit at the initial state (the carry before the first step is 0). From step
3000 a hinge term with weight 0.1 pushes every pre-activation away from zero by at least 1.0,
so that rounding to integers cannot flip a decision. Held-out accuracy is measured on 2000
random pairs at lengths 16, 64 and 128, with the hard threshold.

Training curve of the chosen network (H = 4, seed 1, 6000 steps, 9 s on one core; the run is
deterministic, a rerun gave identical weights):

| step | loss | L16 bits / whole sums | L64 bits / whole sums | L128 bits / whole sums |
| --- | --- | --- | --- | --- |
| 500 | 0.548 | 0.714 / 0.004 | 0.740 / 0.000 | 0.744 / 0.000 |
| 1000 | 0.347 | 0.908 / 0.215 | 0.930 / 0.017 | 0.933 / 0.002 |
| 1500 | 0.225 | 1.000 / 1.000 | 1.000 / 1.000 | 1.000 / 1.000 |
| 3000 | 0.079 | 1.000 / 1.000 | 1.000 / 1.000 | 1.000 / 1.000 |
| 6000 | 0.016 | 1.000 / 1.000 | 1.000 / 1.000 | 1.000 / 1.000 |

What was tried, in order (full numbers in `sweeps_summary.txt`; the run directories named below are not in the repository):

1. `sweep1`: hard (threshold + surrogate) and soft (sigmoid with slope 2 in the forward pass,
   thresholded at test time), H in {4, 8, 16}, 3 seeds, carry supervised after every step.
   15 of 18 reached 100% at lengths 16, 64 and 128 (the misses: soft H = 16, seeds 0 and 1;
   hard H = 4 seed 0 never left 78% bits). But after freezing only 6 of 18 passed the
   finite-state check. The hard-trained ones froze with a pre-activation of exactly 0 somewhere
   on a reachable transition, and most failed because the carry read-out at the initial state
   was 1: training had never shown it the initial state.
2. `sweep2`: carry supervised only after the last step (hard mode). Same length
   generalization (8 of 9), same failure after freezing (2 of 9 passed).
3. `sweep3`: supervising the carry at the initial state fixed the hard runs: all H = 8 and
   H = 16 hard runs passed (margin still 0). A hinge margin term applied from step 1 (weight
   0.3) stopped every run from learning at all (12 of 12 failed).
4. `sweep4`: the hinge term applied only from step 3000 (weight 0.1): 17 of 18 runs pass the
   check with margins 14 to 28. The one miss is hard H = 4 seed 0, which never learned under
   any setting. The chosen network is hard H = 4 seed 1 (5 reachable states, margin 27); the
   H = 16 companion is hard seed 0 (11 reachable states, margin 23).

## Freezing (step 2)

`freeze_check.py`: each affine layer (recurrent; sum bit; carry) is scaled jointly so its largest
entry in absolute value is 127, then rounded. A joint positive scale does not change the sign of
any pre-activation, so the only error is rounding. The frozen weights are `network/frozen_h4.npz`
and `network/frozen_h16.npz`; the float weights are `network/trained_h4.npz` and
`network/trained_h16.npz`. The H = 4 integer weights:

    Wh  = [[-12, 47, 39, -63], [-2, 18, 7, -80], [-2, 15, 14, -84], [4, -10, -17, 82]]
    Wxa = [-6, -90, -99, 92]     Wxb = [-2, -90, -100, 92]     bh = [36, 118, 127, -119]
    Wo  = [-127, 63, 80, -120]   Woa = 125   Wob = 125         bo = -73
    Wc  = [28, -41, -34, 127]    bc = -65

## The finite-state check (step 3)

`freeze_check.py` enumerates the states reachable from `h0` under the 4 input pairs and checks
that the carry read-out `phi(h) = [Wc h + bc > 0]` satisfies `phi(h0) = 0`,
`phi(step(h, (a, b))) = maj(a, b, phi(h))` and `out(h, (a, b)) = a xor b xor phi(h)` on every
reachable state and input. The same check with phi given as a table built by breadth-first
search is done at the same time. For the H = 4 network: 5 reachable states
(0000 carry 0, 1110 carry 0, 1001 carry 1, 0110 carry 0, 0001 carry 1), the check holds, and the
smallest pre-activation in absolute value on a reachable transition is 27. For H = 16: 11
reachable states, margin 23. No single change of any one integer weight by 1 breaks the H = 4
network's check; 22 single sign flips do (20 among the matrix and vector entries, plus the two scalar biases bo and bc; a review on 2026-10-16 found the two scalar flips that the first count skipped).

`check_long.py` runs the frozen integer network on random pairs: 200 of 200 correct at lengths
8, 16, 64, 128 and 1000, and 5 of 5 at length 10,000. This is a sanity check, not the proof.

## The Lean proof (steps 4 and 5)

`lean/RnnAdder/Network.lean` (189 lines) defines `dotB`, `thr`, `step`, `out`, `carry`, `run`,
`runState`, `finalCarry`, the specification `addBits` / `carryOut` (the ripple-carry adder with
carry-in), the certificate `transOk : Net -> Bool`, the induction, and `bitsToNat` with the
arithmetic reading. It is parametric over a `Net` structure of integer weights, an initial state
and the explicit list `reach`; nothing in it depends on the trained numbers.
`lean/RnnAdder/Trained.lean` (generated by `gen_lean_rnn.py`) holds the weights as `.ofNat` /
`.negSucc` literals and the 5 reachable states, proves `transOk net = true` by
`decide +kernel`, and instantiates the three theorems:

    theorem sums_correct (xs : List Input) : run net net.h0 xs = addBits false xs
    theorem carry_correct (xs : List Input) : finalCarry net net.h0 xs = carryOut false xs
    theorem adds (xs : List Input) :
        bitsToNat (run net net.h0 xs) + 2 ^ xs.length * (if finalCarry net net.h0 xs then 1 else 0)
          = bitsToNat (xs.map Prod.fst) + bitsToNat (xs.map Prod.snd)

`xs` ranges over all lists of bit pairs, of every length. `Trained16.lean` states the same three
theorems for the 16-unit network.

`run_check.sh` (output in `run_check.log`, clean build): `lake build` 3.3 s; `leanchecker`
replays of `RnnAdder.Network`, `RnnAdder.Trained`, `RnnAdder.Trained16` all OK (0.7 s, 0.5 s,
1.3 s); both planted faults rejected (`FaultA`: `Wh[0][3]` from -63 to 63; `FaultB`: `Wc[3]`
from 127 to -127; each gives "Tactic `decide` proved that the proposition transOk net = true is
false"); `#print axioms` on all three theorems: `[propext, Quot.sound]`, a subset of the
standard three (`Classical.choice` is not used); no `sorry`, `native_decide`, `axiom`,
`opaque`, `implemented_by`, `extern` or `skipKernelTC` in the sources. `verify_lean_weights.py`
confirms the Lean literals equal the npz files without Lean; `eval_check.lean` shows Lean's
`run` and numpy agree on 13 + 7 = 20 and 255 + 1 = 256.

## What is not done

- The carry read-out was supervised during training (after every step and at the initial
  state). The sum bits are the task; the carry read-out is an auxiliary head that the proof
  uses as the map from states to carries. A network trained with the carry supervised only
  after the last step passed the check in 2 of 9 runs (`sweep2`), before the initial-state
  supervision and the margin term were added; that setting was not rerun with them.
- Hard H = 4 seed 0 never learned (78% bits) under any setting tried.
- The certificate does not cover states outside `reach`; the theorems are about runs from
  `h0`, which is all the specification asks.
- No second independent checker beyond `leanchecker` (nanoda is not installed here), and the
  toolchain binary was not compared with the official release.
- Nothing ran on Modal or Prime Intellect (no credentials in this container; none was needed).

## Files

| Path | What it is |
| --- | --- |
| `train_rnn.py` | numpy BPTT trainer (hard or soft forward pass, margin term, carry supervision) |
| `freeze_check.py` | freezing to integers and the finite-state check in Python |
| `gen_lean_rnn.py` | writes a frozen network and its reachable states into Lean |
| `verify_lean_weights.py`, `check_long.py`, `eval_check.lean` | cross-checks outside the proof |
| `lean/` | the Lean package (`RnnAdder/Network.lean`, `Trained.lean`, `Trained16.lean`, `expected_fail/`) |
| `run_check.sh`, `run_check.log` | the full check and its output |
| `network/` | float and frozen weights, the rerun log of the chosen configuration |
| `sweeps_summary.txt` | every training attempt (four rounds, 81 runs) and its result after freezing; the run directories themselves are not in the repository |

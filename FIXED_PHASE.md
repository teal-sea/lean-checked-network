# Networks built from a formula, checked by the kernel

Status of each claim is stated per line: **kernel-checked** (Lean 4's kernel accepted the proof,
standard axioms only, replayed by `leanchecker`), **measured** (a numpy computation), or
**derived** (an argument on paper, checked numerically, not written in Lean).

## The construction

Gromov (2023, arXiv:2301.02679, eqs. 6 to 16) gives analytic weights for this repository's
two-layer square network: a neuron at frequency `k` has `E1[a] = cos(2πka/p + φ₁)`,
`E2[b] = cos(2πkb/p + φ₂)`, `W2[c] = cos(2πkc/p + φ₁ + φ₂)`, with **random** phases. Expanding the
score `Σ_h W2[c,h] (E1[a,h] + E2[b,h])²` gives nine families of waves (his equation 11); the one in
`a + b − c` is the answer and the other eight cancel only on average over random phases, which is
why his solution is approximate and needs large width.

**Fix the phases on a cycle and the eight families cancel exactly.** Each unwanted family carries a
phase `uφ₁ + vφ₂` with `(u, v)` in `{(1,−1), (3,1), (−1,1), (1,3), (2,2), (0,−2), (2,0), (1,1)}`. Take,
per frequency, six neurons with `φ₁ = 2πj/6` and `φ₂ = 4φ₁` for `j = 0, …, 5`. Then every unwanted
family has phase `(u + 4v)·2πj/6` with `u + 4v` never divisible by 6 (the eight values are −3, 7, 3, 13,
10, −8, 2, 5), so each sums to zero over the cycle, and what survives is exactly

    score(a, b, c) = 3 · Σ_{k ∈ S} cos(2πk(a + b − c)/p)

for any frequency set `S`. (The first version used eight neurons per frequency on a 4 × 2 grid of
phases; six on a cycle is smaller and the same argument. The grid is the version proved for every
modulus in `phasegrid/`, below.) So the real network adds mod `p` whenever
the **gap**

    g(S) = |S| − max_{s ≢ 0 (mod p)} Σ_{k ∈ S} cos(2πks/p)

is positive. For `S` = all frequencies `1 … ⌊(p−1)/2⌋`, the sum of roots of unity gives `g = p/2` for odd
`p` and `g = p/2 − 1` for even `p`.
Rounding every weight to an integer at scale `M` moves each neuron's score by at most about `6M²`,
the margin is `3g(S)M³`, two scores are compared, so `M > 24|S|/g(S)` is enough (a crude bound; the
measured minimum scales are far lower). With `S` every frequency that is `M ≥ 24` at odd `p`, and
`M = 25` covers every `p ≥ 3`. The exact cancellation was checked numerically to
floating-point noise (largest deviation `4.5 × 10⁻¹³`) before any integer network was built.

**Status: derived here; the grid version is proved on `main`.** The theorem for every `p`, every
`S` with `g(S) > 0` and every large enough `M` is proved in Lean 4 over Mathlib for the 4 × 2 phase
grid (eight neurons per frequency): `PhaseGrid.adds_mod_p` in `phasegrid/mathlib/`, merged in PR #2
on 2026-10-16 10:24Z and reviewed twice; `phasegrid/README.md` has the statement, the proof and its
costs, and the section "What is proved, what is not, and what the kernel costs" below has the
summary. The six-phase cycle version is derived here and not yet proved in general. What this file
does is the finite thing: build the integer network for `p = 113` and let the kernel check every
pair, exactly as it checks the trained network.

## The networks, `p = 113`

| Network | Frequencies `S` | Neurons | Weight scale `M` | Weights | Smallest winning margin (measured) | Kernel verdict (2026-10-16) | Same construction in `phasegrid/instances/` |
|---|---|---|---|---|---|---|---|
| `FixedPhase12` | {39, 45}, `g = 0.187` | 12 | 127 | 8-bit | 1,021,168 | **kernel-checked**, `adds_mod_113`, 149 s on 4 cores, standard axioms | none: six-phase cycle, which the grid theorem does not cover |
| `FixedPhase16` | {39, 45}, 8 per frequency (the 4 × 2 grid) | 16 | 127 | 8-bit | 1,416,180 | **kernel-checked**, 152 s, standard axioms | none at this `S` |
| `FixedPhase40` | Nanda et al.'s five key frequencies {14, 35, 41, 42, 52}, `g = 2.41`, 8 per frequency | 40 | 127 | 8-bit | 19,523,208 | **kernel-checked**, 221 s, standard axioms | `P113Nanda5`: same `S`, 40 neurons, at `M = 30` there (margin 245,012) against `M = 127` here, so different integer tables |
| `FixedPhase448` | all 56 frequencies, `g = 56.5`, 8 per frequency | 448 | 25 | 5-bit | 3,514,188 | **kernel-checked**, 4,011 s with its sixteen row files built one at a time (a 448-wide table elaborates at about 5 GB), standard axioms | `P113Full`: same `S`, 448 neurons, `M = 25`, margin 3,514,188; the integer tables are identical (measured, see "Two witnesses" below) |

`{39, 45}` is the first survivor in a search over all 1,540 two-frequency sets at `M = 127`,
ordered by gap; no single frequency survives at `M = 127` (**measured**). One frequency does
survive at `M = 1023`: six neurons with 10-bit weights add mod 113 on every pair (**measured**;
outside the fast evaluator's weight range, so not kernel-checked here). The 448-neuron network is
the one the bound covers for every `p`: `M = 25` satisfies `M > 24|S|/g(S)` when `S` is every
frequency, so 5-bit weights add mod `p` for every modulus, derived, and kernel-checked at `p = 113`.

Each network was generated by `make_fixed_phase.py` or `make_fixed_phase6.py` into `network/*.npz`
(same keys as the trained network), then `gen_lean.py` wrote its `Weights.lean`, `Table.lean`,
sixteen `Rows*.lean` files and `AllInputs.lean`, and `run_lean_fixed_phase.sh` built them, printed their axioms
and replayed every module with `leanchecker`. `lean_run_fixed_phase.log` is the full run of 2026-10-16: the builds with their
wall times, the axiom audit, the planted fault, and the `leanchecker` replay of every module;
`lean_run_fixed_phase_small.log` is the first audit of the three small networks, kept for the record.

## Other moduli, same formula

The construction is stated for every modulus, prime or not, and the bound `M > 24|S|/g(S)` with `S`
every frequency gives `M = 25` for all of them. Two cheap instances, kernel-checked the same way
(`Mod7All.adds_mod_7`, `Mod12All.adds_mod_12`, standard axioms, 10 seconds for both on 4 cores,
2026-10-16):

| Modulus | Frequencies | Neurons | Weights | Smallest winning margin (measured) | Kernel verdict | Same construction in `phasegrid/instances/` |
|---|---|---|---|---|---|---|
| 7 | all 3 | 24 | 5-bit (`M = 25`) | 219,400 | **kernel-checked** | `P7Full`: 24 neurons, `M = 25`, margin 219,400; the integer tables are identical (measured, below) |
| 12 (composite) | all 5 | 40 | 5-bit (`M = 25`) | 308,750 | **kernel-checked** | none |
| 257 | {114, 125}, the first survivor of all 8,128 two-frequency sets, six phases each | 12 | 8-bit (`M = 127`) | 375,872 | **kernel-checked**, 66,049 pairs in 32 row files, 1,582 s, standard axioms | none: six-phase cycle |

**Two witnesses of one construction (measured 2026-10-16).** `make_fixed_phase.py` and
`phasegrid/instances/gen_phase_grid.py` were written separately, use the same 4 × 2 grid in the same
neuron order, and at the same `(p, S, M)` produce the same integers: `np.array_equal` on the `E1q`,
`E2q` and `W2q` arrays of `network/fixedall.npz` and
`phasegrid/instances/PhaseGridInstances/P113Full/P113Full.npz` is true for all three (113 × 448
entries each), and likewise for `network/mod7_all.npz` and `P7Full/P7Full.npz` (7 × 24). The
`Weights.lean` files of `P113Full` and `P7Full` parse to those same integers, and `verify_weights.py`
checks `FixedPhase448` and `Mod7All` against the `.npz` files, so the four Lean weight files hold two
copies of two networks. The Lean encodings differ: `FixedPhase448` (namespace
`LeanCheckedNetwork.FixedPhase448`, `lean/LeanCheckedNetwork/FixedPhase448/`) writes each table as one
list literal and checks a row with one `decide +kernel`; `P113Full` (`PhaseGridInstances.P113Full`, its
own Lake package) writes 113 row definitions per table and five `decide +kernel` calls per row; `Mod7All`
and `P7Full` differ in package, namespace and the split of the seven rows into four row files against
two. Each encoding was built and replayed by `leanchecker` on its own (`lean_run_fixed_phase.log`, 197 of
197 modules; `phasegrid/instances/replay.P113Full.out`, 21 of 21), so the 448-neuron network and the
24-neuron one each have two independent kernel verdicts. `FixedPhase40` and `P113Nanda5` share the
frequency set and the width but not the scale (`M = 127` against `M = 30`), so their tables differ in
4,500 of the 4,520 entries of each table: two networks, each kernel-checked once.

## The planted fault

Beside every proved network this repository keeps a variant the kernel must reject. `FaultFixed12`
is `FixedPhase12` with one read-out weight raised by 22 (`W2[104][7]`, from 1 to 23, still inside
[-128, 127]); that flips its tightest pair (11, 35) to the answer 104 and 15 others, 16 of 12,769
wrong (measured). `lean/expected_fail/FaultFixed12Row.lean` is the row-11 proof for that network;
`run_lean_fixed_phase.sh` requires it to fail with a kernel error. It does: *"(kernel) application
type mismatch"* (2026-10-16). The 40-neuron network's smallest margin, 19,523,208, exceeds the
most one weight change inside [-128, 127] can shift the gap between two scores, 254 × 255² =
16,516,350, so no single weight change can flip any of its answers (derived, the same argument as
the trained network's); the 12- and 16-neuron networks are below that line, which is why the fault
is planted in the smallest one.

## Counting, not only proving

**Open item: `Count.lean` and the sweep's wrong-set statement say one thing in two shapes (plan
recorded 2026-10-16, no Lean changed).** The sweep route (`sweep/`, on `main` since PR #1) gives a wrong
network the statement "wrong on exactly these `k` pairs": `answer_iff_not_wrong` (the answer is right
if and only if the pair is not in the explicit list `wrongPairs`), with `wrongPairs_length = k`,
`wrongPairs_strictLex` (so `wrongPairs.Nodup`, by `nodup_of_strictLex`) and `wrongPairs_in_range`.
Those per-network theorems are written into each generated package by `sweep/run_one.py`; what
`sweep/WrongSet.lean` holds is the list lemmas they rest on (`rowsToPairs`, `mem_rowsToPairs`,
`strictLex`, `nodup_of_strictLex`). `Count.lean` gives the number only, row by row (`right_on_N`). The
first implies the second: a strictly ordered, duplicate-free, in-range list of exactly `k` wrong pairs
among `p · p` gives `count = p · p − k`. So the generated wrong-set statement is the one to keep. The
plan: add to `WrongSet.lean` a lemma `right_on_count` that takes the three generated facts as
hypotheses and concludes `count E1 E2 W2 p = p * p − wrongPairs.length` (`count` and `rowCount` as
`Count.lean` defines them, so the generated package would carry that definition too; the proof is list
counting, with no new kernel evaluation), have `run_one.py` instantiate it, and regenerate the six
learning-curve modules `lean/LeanCheckedNetwork/H64Step*/` through the sweep route (`run_one.py`'s
generator, which already writes `wrongRows` per row) the next time anyone touches them, so that each
checkpoint states which pairs it gets wrong and the count follows. That regeneration is about 40 minutes of
kernel time (the six count builds took 372 to 382 s each on 4 cores, 2,269 s in all,
`LEARNING_CURVE.md`; the sweep route is also one kernel evaluation per row) and is not in this change.
The same item is recorded in `sweep/README.md`.

`adds_mod_p` says a network is right on every pair. A trained network part way through training
is right on some number of pairs, and that number is what a study of training would certify, run
by run and checkpoint by checkpoint. `lean/LeanCheckedNetwork/Count.lean` gives the count the same
treatment as the answer, row by row so that each kernel evaluation stays small (a single
evaluation over all 12,769 pairs was killed at about 8 GB; one row needs a few hundred MB):
`fastRowCount` counts the correct `b` for one `a` with the packed evaluator, `rowCount_eq_fastRowCount`
proves it equals the count on the network itself whenever the evaluator's cheap checks pass on
that row (`rowOk`), and `count` is the sum over rows. The first instance is the planted fault,
`FaultFixed12.right_on_12753`: 113 row theorems, each one kernel evaluation, then the sum. The
network is right on exactly 12,753 of the 12,769 pairs, 16 wrong, **kernel-checked**, standard axioms.
The same machinery then gave six checkpoints of a training run their exact scores: `LEARNING_CURVE.md`.

## What is proved, what is not, and what the kernel costs

**The theorem in Lean over Mathlib: proved, on `main`.** `phasegrid/mathlib/` (PR #2, merged
2026-10-16 10:24Z, reviewed twice) proves `PhaseGrid.adds_mod_p`: for every `p > 0`, every frequency
list `S` with a positive gap `g`, and every `M` with `24|S| < M·g`, the phase-grid network (eight
neurons per frequency, `φ₁ ∈ {0, π/2, π, 3π/2}`, `φ₂ ∈ {0, π/2}`, weights `round(M cos …)`) answers
`(a + b) mod p` on every pair, with `answer` the definition in `Network.lean` copied verbatim;
`adds_mod_p_full`: every `p ≥ 3`, all frequencies, every `M ≥ 25`; and `adds_mod_p_tables`: any
integer tables within 1/2 of the analytic weights. 42 theorems (the `#print axioms` list in
`phasegrid/mathlib/verify2.sh`), every one on `[propext, Classical.choice, Quot.sound]` or a subset,
every module replayed by `leanchecker`. The CI job `phasegrid` rebuilds the project from the Mathlib
cache, replays it and prints the axioms on every push, and rejects a planted fault and, since PR #3,
two faults that are wrong only at the last pair of a row. The corrections that proof forced on the
first draft of this file are folded in above (eight unwanted families, `M ≥ 24` at odd `p`, the
even-`p` gap, no primality). Statement, proof and costs: `phasegrid/README.md`.

**What is not proved.** The grid version is proved; the six-phase cycle of this file (`φ₂ = 4φ₁`,
six neurons per frequency, the construction of `FixedPhase12` and `Mod257Min`) is derived here and
kernel-checked at those two instances, and its general theorem is not written. It is the same proof
with the sum of `exp(2πi j m/6)` over `j = 0..5` (zero unless `6 ∣ m`) in place of the grid sums and
`3 Σ cos` in place of `4 Σ cos` in `realScore_eq`; open, recorded here. The constant 24 is crude; what
the instances above show is that the true threshold is far lower (the 448-neuron network survives at
`M = 8`, measured; `phasegrid/README.md` measures `M = 1` for the full set at every odd `p` it tested
and leaves `M = 2` for every odd `p ≥ 5` as the open statement `fullSetWorksAtTwo`). A companion statement
for a trained network replaces each column by a wave plus a remainder with a norm bound, as
`MECHANISM.md` does in Python; the theorem then certifies a trained network from a finite check of
its hypotheses rather than from 12,769 evaluations, which is the compact proof of Gross et al. (2024)
inside a proof assistant.

**Kernel cost, measured 2026-10-16 on 4 cores** (build of the 16 row files plus the table check,
`lake build …AllInputs`, no replay): 12 neurons 149 s, 16 neurons 152 s, 40 neurons 221 s; the
trained 128-neuron network took about 13 minutes per network in this repository's own README
timing. So the cost is a floor of a couple of minutes plus a few seconds per neuron, as the packed
evaluator predicts: one big-number multiply-add per neuron per input.

## Why it matters next to the trained network

The trained network (`Trained`) is right on every pair and the kernel says so, but the only
explanation the kernel has accepted so far is an ablation (`CircleOnly`). These networks are the
explanation itself, built from the mechanism and nothing else: five numbers and one formula give a
40-neuron network the kernel accepts, two numbers give a 12-neuron one. The width a certified
network needs is governed by `g(S)`, an exponential sum over the frequency set, which is the
quantity that decides how small a trained network could be and still be right.

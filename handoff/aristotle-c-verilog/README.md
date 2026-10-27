# Handoff: Aristotle for C and Verilog, applied to lean-checked-network

Written 2026-10-27 by a Claude Code session under Thomas Lince's direction, the day Harmonic
announced Aristotle for C and Verilog and paused Lean projects on Aristotle. This packet is
everything the next person or agent needs to take the four workstreams below from idea to a
labelled result in this repository. Nothing in `handoff/` changes any proved result.

Status words follow the house rule. **Kernel-checked**: Lean's kernel accepted it, replayed by
`leanchecker`, standard axioms. **Measured**: a Python computation, reproducible from the scripts
here. **Derived**: an argument in exact arithmetic, not in Lean. **Vendor**: a statement on
Harmonic's own pages. **Open**: not established.

## 0. The one-paragraph version

Harmonic's Aristotle now takes C or Verilog, proposes properties, and returns proved / refuted /
open per property with an assumptions list, in CI, consumption-priced (**vendor**). This
repository has kernel-checked theorems about integer networks and no C and no Verilog. Four
workstreams below would put the same integer objects into C and RTL and prove things about them
that no verified-ML result has stated: the interpretability explanation as a hardware equivalence,
proved immunity to weight bit flips, a trained state machine proved for all time, and one object
with kernel, C and RTL proofs with every trust boundary named. There are $500 of credits until
2026-11-27. One question gates how any of it can be labelled: **does Aristotle export an artifact
an independent checker can replay?** Answer that on day one (section 2).

## 1. Context in five bullets

- **Vendor.** Announcement, 2026-10-27: Aristotle "proposes properties from your code, then
  reports which ones it proved, which it didn't," and "the assumptions each proof rests on." C:
  "functional correctness and the absence of certain classes of undefined behavior." Verilog:
  "control-path properties such as liveness and safety" and "mathematical data-path properties."
  "No spec is required"; properties in plain English. "Every proof is machine-checked." The
  checker, spec language and proof format are not named anywhere public.
- **Vendor case studies.** LibTomMath (C): two memory bugs found, repaired code proved against
  specs for results, memory safety, errors and stored values; optimized code re-proved. Tensordyne
  (Verilog): 241 properties on a 1.24M-flop block, 185 proved, 56 refuted with counterexamples
  25,000 to 110,000 cycles after reset, "no cycle bound."
- **Circumstantial evidence the substrate is Lean 4**, at least for hardware: Harmonic's hardware
  formal verification hire described building "a flow based on the Lean theorem prover"; its
  public talks show circuits as a Ruby DSL embedded in Lean 4 with Aristotle proving Lean theorems;
  Harmonic's code-verification benchmark result (VERINA, 96.8 percent) is Lean-based. Counter
  evidence: the Tensordyne scale and depth look like an industrial model checker. Unresolved.
- **The Lean pause** (email to Thomas, effective 2026-10-27, "temporary", no date) is not
  documented publicly. Aristotle was used heavily on this project; the repository carries no trace
  of it, and the README's authorship line names only Claude Code and Codex. See section 8.
- Full research note with sources: `research-note-2026-10-27.md` in this directory.

## 2. Day one: the gating test

Before building anything, spend a few dollars learning what comes back.

1. Sign in at aristotle.harmonic.fun, create one C project with the 12-neuron network
   (section 3 says how to generate it), submit, and let Aristotle propose properties.
2. Record verbatim: every property it proposed, each verdict, the assumptions list, the job id,
   the cost, the wall time.
3. Look for an exportable artifact. Three outcomes, each with its label:
   - **Lean objects or sources.** Replay with `leanchecker` under the pinned toolchain, print the
     axioms, check the statement text. If it passes, the result can be labelled **kernel-checked**
     with Aristotle's C semantics named as an assumption, the same way TorchLean's semantics are
     named in `acas/`.
   - **A certificate in another format** (SMT proof, model-checker witness, SAT proof). Identify the
     checker, whether it is open, and whether it can be run here. Label: **checked by <tool>**, with
     the tool and its version named, a class this repository has not used before.
   - **No artifact, only a verdict and a report.** Label: **tool verdict (Aristotle, date, job id)**.
     This is weaker than anything currently in the README and must be presented as such. The C and
     Verilog themselves remain useful: they can be checked by other tools later.
4. Write the outcome into `handoff/aristotle-c-verilog/runs/2026-xx-xx-gating.md`. Every later run
   gets the same kind of file (section 6).

## 3. Shared groundwork

All four workstreams need the same generated code and the same pinning discipline.

### 3a. Integer widths (measured, `network/*.npz`)

A direct C port of `Network.lean`: `hidden[h] = (E1[a][h] + E2[b][h])^2`,
`score[c] = sum_h W2[c][h] * hidden[h]`, answer = first index of the largest score.

| network | p | H | max abs weight | hidden bound | per-term bound | score bound | int32 | min winning margin |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | ---: |
| trained | 113 | 128 | 127 | 64,516 | 8,193,532 | 1,048,772,096 | yes | 32,654,491 |
| circle-only | 113 | 128 | 130 | 67,600 | 7,909,200 | 1,012,377,600 | yes | 1,980,696 |
| FixedPhase12 | 113 | 12 | 127 | 64,516 | 8,193,532 | 98,322,384 | yes | 1,021,168 |
| FixedPhase16 | 113 | 16 | 127 | 64,516 | 8,193,532 | 131,096,512 | yes | 1,416,180 |
| Mod12All | 12 | 40 | 25 | 2,500 | 62,500 | 2,500,000 | yes | 308,750 |
| Mod257Min | 257 | 12 | 127 | 64,516 | 8,193,532 | 98,322,384 | yes | 375,872 |

Hidden entries need 32 bits (they exceed int16). Every score fits a 32-bit signed accumulator
with headroom, so "no signed overflow" is a true and provable property of the straightforward C.
Note the circle-only weights reach 130: an 8-bit ROM cannot hold them; use 9-bit cells.

### 3b. What to generate

- `c/mlp_mod.c`, `c/mlp_mod.h`: one function `int mlp_answer(const net_t *n, int a, int b)` over
  `int32_t` tables with `int32_t` accumulators, first-index argmax, plus one generated header per
  network from the npz files (reuse the npz reading in `gen_lean.py`; keep `.negSucc`-style sign
  handling out of it, C has signed literals).
- `verilog/mlp_mod_tables.v`: the weight-table RTL, combinational or two-stage, ROMs for E1, E2,
  W2, 12 or 128 squarers, p dot products, a first-index argmax tree. Parametrise p, H and the ROM
  width. A `fault` port (table id, row, column, bit, enable) that XORs one ROM cell, for
  workstream 2; with `enable = 0` it must be the plain network.
- `verilog/rnn_adder.v`: the H = 4 recurrent adder (section 4, workstream 3).
- Tests, before any submission: a Python differential test that the C and the RTL (via a
  simulator, Icarus or Verilator) agree with `verify_weights.py`'s evaluation on all p*p pairs, and
  that the generated tables are byte-identical to `E1q`, `E2q`, `W2q`. Pin the npz SHA256s the way
  `transformer/` pins its data. The proofs are about those bytes; the C and RTL must be too.

### 3c. Properties to submit, exact wording

C, per network:

- P1 (safety): for all integers a, b with 0 <= a, b < p, `mlp_answer` executes without undefined
  behavior: no signed overflow, no out-of-bounds read, no uninitialised read.
- P2 (function): for all 0 <= a, b < p, `mlp_answer(a, b) == (a + b) % p`.
- P3 (only if the artifact is Lean-based): for all 0 <= a, b < p, `mlp_answer(a, b)` equals
  `LeanCheckedNetwork.answer E1 E2 W2 a b` from `lean/LeanCheckedNetwork/Network.lean` on the same
  tables. P3 composed with the kernel-checked `adds_mod_113` is the end-to-end statement.

Verilog, per network: P2 as a data-path property over all input pairs, and the fault property of
workstream 2.

Submit each network twice: once letting Aristotle propose properties with no hints (record what
it thinks matters), once with P1 to P3 stated.

## 4. The four workstreams

### Workstream 1. The explanation is the circuit: mechanism RTL and its equivalence

**Goal.** Build the RTL from the circle mechanism rather than from the weight tables, and prove
its relation to the weight-table RTL and to the correctness theorem.

**Why it is new.** Mechanistic interpretability says "this network computes by rotating on a
circle." In hardware that is a concrete datapath: rotate the input by k steps on a p-point circle,
add a phase, look up a cosine, square, correlate with the readout cosines. An equivalence proof
between that datapath and the weight tables is the explanation stated as a hardware theorem, and
the correctness proof of that datapath is the circle-only theorem in silicon. No search on
2026-10-27 found anything like it.

**Tier A: FixedPhase12** (`network/fixed12.npz`, kernel-checked `FixedPhase12.adds_mod_113`).
The construction (`make_fixed_phase6.py`): neuron h = 6 i + j has frequency k_i in {39, 45} and
phases phi1 = 2 pi j / 6, phi2 = 4 phi1; E1[x][h] = round(127 cos(2 pi k x / 113 + phi1)), E2 with
phi2, W2 with phi1 + phi2. All angles are multiples of 2 pi / 678 (678 = lcm(113, 6)), so one
678-entry cosine ROM indexed by `6 * ((k * x) mod 113) + 113 * m * j mod 678` with m = 1, 4, 5
should reproduce all three tables.

**Measured finding, 2026-10-27 (`mechanism_rom_check.py`):** it does not, by 6 cells out of 4,068
(2 in E2, 4 in W2), each off by 1, all at the three angles pi/3, 2 pi/3 and 5 pi/3 where
127 cos equals exactly plus or minus 63.5 and floating-point noise in the unreduced angle decided
the rounding. The tables are not even self-consistent at those three angles (both 63 and 64 occur).
So the clean statement "weight-table RTL equals shared-ROM RTL" is false for the kernel-checked
network as it stands. `Mod257Min` (six phases, grid 1,542) has the same defect: 6 of 9,252 cells,
2 per table, off by 1. The eight-phase networks (`FixedPhase16`, `Mod12All`) are not covered by
the check. Two honest ways forward:

1. **Recommended.** Define a new fixed-phase network from the 678-entry ROM (the ROM is the
   definition, no unreduced cosines), kernel-check it by the existing route (about 139 s on 4
   cores per `phasegrid/smallest-networks.md`; `gen_lean.py` and `run_lean_fixed_phase.sh` already
   do this for any npz), then prove in Verilog that the mechanism RTL equals the weight-table RTL
   of that network, exactly, and that both add mod 113. Name it, for example, `FixedPhase12Rom`.
   The margin (about 1.02 million) dwarfs a handful of plus or minus 1 cell changes, so it will be
   right everywhere; check with `verify_weights.py` first.
2. **Fallback.** Keep `FixedPhase12` and give the mechanism RTL a 6-entry correction table. The
   equivalence is then exact but the story is uglier.

Properties: E1 (equivalence): for all a, b < 113, mechanism RTL output equals weight-table RTL
output. E2 (correctness): both equal (a + b) mod 113. Expected: both proved. Cost: small, the
circuits are tiny.

**Tier B: the trained 128-neuron network.** The circle-only tables (`network/circle_only.npz`,
kernel-checked `CircleOnly.adds_mod_113`) and the residual `trained - circle_only` (measured max
abs 72) split the trained ROMs exactly. Build the trained RTL with ROM = circle ROM + residual ROM
(9-bit circle cells). Properties: B1 the sum of the two ROMs is the trained table (structural,
trivial, states the split); B2 output with residual zeroed equals (a + b) mod 113 (the circle-only
theorem, expected proved); B3 output with circle zeroed equals (a + b) mod 113 (expected refuted;
measured: the residual-only network is wrong on 12,719 of 12,769 pairs); B4 the full network
equals (a + b) mod 113 (expected proved). B2 and B3 together are the ablation pair from the README,
now as hardware verdicts with counterexamples. Stretch: `MECHANISM.md`'s certificate, that the
residual's effect on every score gap is below the circle path's margin, restated as a bounded
property; this is the one derived result in the repository that is "not yet in Lean", and a
machine check of it in any form would be its first.

### Workstream 2. Proved immunity to weight faults

**Goal.** Prove, or exactly refute, that single faults in the weight memory cannot change any
output.

**Why it is new.** The README's derived result says no single weight change within range can flip
any answer of the trained network, because the smallest margin (32,654,491) is about twice the
largest shift one change can make to a score gap (254 x 255^2 = 16,516,350). In RTL this is a
single-event-upset theorem about a learned model's accelerator, quantified over every input and
every fault site. Safety-critical ML has no proved statement of this kind for a trained network.

**Measured baselines (`fault_census.py`, 2026-10-27).** "Flips" means at least one of the p*p
answers changes.

| network | fault model | faults that flip | of | cells with a flipping value |
| --- | --- | ---: | ---: | ---: |
| trained | single bit, any of 3 tables | 0 | 347,136 | 0 of 43,392 |
| trained | any value, W2 only | 0 | 3,688,320 | 0 of 14,464 |
| trained | any value, E1 and E2 | derived 0 (README bound) | 7,376,640 | not run (about 47 billion evaluations) |
| FixedPhase12 | single bit, any of 3 tables | 8,578 | 32,544 | 3,996 of 4,068 |
| FixedPhase12 | any value, any of 3 tables | 751,070 | 1,037,340 | 4,068 of 4,068 |

Regenerate: `python3 handoff/aristotle-c-verilog/fault_census.py network/trained.npz bits`
(about 8 minutes), `... network/fixed12.npz values` (about 1 minute).

Properties (Verilog, using the fault port as free inputs held constant, the standard way formal
tools quantify over a fault site):

- F1: for all a, b < p and all single-bit fault sites (table, row, column, bit), output equals
  (a + b) mod p. Expected: **proved** for the trained network, **refuted** for FixedPhase12.
- F2: the same with the faulted cell set to any value. Expected: proved for the trained network;
  refuted for FixedPhase12.
- F3 (optional, if the tool can count or if it can be posed as a family): the exact number of
  flipping single-bit faults for FixedPhase12 is 8,578. This is the built-in control: whatever
  Aristotle refutes must agree with the census. Any disagreement is a bug on one side and must be
  resolved before anything is written up.

Note the same F1 could be asked of the C with a fault-injecting wrapper, but it is a hardware
question; keep it in Verilog.

### Workstream 3. The trained recurrent adder proved for all time

**Goal.** The H = 4 recurrent network (`rnn/network/frozen_h4.npz`, kernel-checked
`RnnAdder.Trained.adds` for inputs of every length) as a sequential circuit, with its correctness
proved with no cycle bound.

**Why it is new.** The Lean proof is a finite check of 5 reachable states under 4 input pairs
followed by induction on the input list. In RTL the same fact is an unbounded-time safety property
of a trained state machine, exactly the class Harmonic advertises. A gradient-trained circuit
proved correct for every clock cycle is a clean first, and it exercises the "no cycle bound" claim
on an object whose proof is already known.

**The circuit.** State h is 4 bits. Per cycle with inputs (a, b):
`h' = [Wh h + Wxa a + Wxb b + bh > 0]` entrywise, `sum = [Wo h' + Woa a + Wob b + bo > 0]`,
`carry = [Wc h + bc > 0]`, h0 = 0000. Weights in `rnn/README.md` and the npz. Pre-activations fit
int16 with room (the largest row sum is a few hundred). Reachable states: 0000, 1110, 1001, 0110,
0001. Margin 27 on every reachable transition (measured in `rnn/`).

Properties:

- R1: from reset, for every input sequence, `sum = a xor b xor carry_in` every cycle, and carry
  follows majority(a, b, carry_in), with carry 0 at reset. Equivalently: equivalence against a
  one-line ripple-carry serial adder reference. Expected: proved, unbounded.
- R2: the two planted faults from `rnn/lean/expected_fail` (`Wh[0][3]` from -63 to 63; `Wc[3]`
  from 127 to -127) are refuted with a counterexample trace. Expected: refuted. The traces are
  worth keeping; they are the hardware form of the kernel rejections.
- R3: the H = 16 companion (`frozen_h16.npz`, 11 reachable states, margin 23), same properties.

### Workstream 4. One object, three proofs, every boundary named

**Goal.** For one network, the chain: kernel-checked theorem about the integer object; C proved
equal to the Lean `answer` on the same bytes and free of undefined behavior; Verilog proved equal
to the same specification. Then a statement in the README in the house style, with the trust
boundary spelled out exactly as `acas/README.md` does.

**Why it is new.** No search found a neural network with a kernel-checked correctness theorem, a
verified C implementation and a verified RTL implementation of the same object.

**Target.** FixedPhase12 (or `FixedPhase12Rom` from workstream 1) first because it is cheapest;
the trained 128-neuron network second because it is the headline object. Not the transformer (its
packed integer program works near 2^200, a C port needs bignum arithmetic and the no-UB story
becomes a library-correctness story) and not ACAS Xu (the theorem is over exact reals and
excludes IEEE floats by design; a fixed-point implementation with proved error bounds is a project
of its own).

**The statement template** (fill after the gating test decides the label):

> For the network `<name>` with weights `<npz sha256>`: Lean's kernel proves `answer a b = (a + b) % p`
> for all a, b < p (`<theorem>`, standard axioms, replayed by `leanchecker`). The C function
> `mlp_answer` in `c/<file>` on the same tables is <label> to equal `answer` and to execute without
> undefined behavior for all a, b < p, under <Aristotle's stated C assumptions, verbatim>. The RTL
> in `verilog/<file>` is <label> to equal `(a + b) % p` on every input pair. The link between the C,
> the RTL and the npz bytes is a byte comparison (`<test>`). Not covered: compilation of the C,
> synthesis of the RTL, timing, and anything about the floating-point checkpoint.

## 5. Order of work and budget guardrails

1. Gating test on the FixedPhase12 C (section 2). Decide the label class.
2. Generate everything in section 3 with the differential tests green. No submission before the
   bytes are pinned.
3. Workstream 2 on FixedPhase12 (expect refutations; check the counts against the census), then
   workstream 2 on the trained network (expect proofs). These two runs are the most informative
   per dollar: one tests refutation fidelity, the other tests a real proof over 347,136 fault
   sites.
4. Workstream 1 tier A, with the `FixedPhase12Rom` kernel check done locally first.
5. Workstream 3.
6. Workstream 1 tier B and workstream 4 on the trained network last; they are the largest
   submissions.

Harmonic publishes no unit prices (**vendor**: "consumption-based"). Record the cost of every job.
Soft stop at $300 spent before starting the 128-neuron runs; if the small runs cost more than
expected, finish workstreams 1A, 2 (FixedPhase12) and 3 and leave the rest documented as open.
Credits expire 2026-11-27.

## 6. Reporting discipline

For every submission, one file `handoff/aristotle-c-verilog/runs/<date>-<workstream>-<network>.md`
with: the exact inputs (file hashes), the prompt or property text verbatim, every property
Aristotle proposed, every verdict verbatim, the assumptions list verbatim, counterexamples in
full, job id, wall time, cost, the artifact (what, where saved, replay result if any). Measured
numbers in this packet are the cross-checks: a verdict that disagrees with a census number is a
finding, not a rounding error.

When something is written up in the main README or a STATUS file, use the labels from section 2
and nothing stronger. "Aristotle proved" is not a label this repository uses; "kernel-checked,
proof produced by Aristotle, replayed by leanchecker" is, if that is what happened.

## 7. Risks and what not to claim

- The whole thing may come back as verdicts without artifacts. Then the C and RTL are still
  worth having and the write-up says "tool verdict". Do not call it a proof in the README.
- Aristotle's C semantics and assumptions (platform, integer widths, memory model) are part of
  every statement. Copy them verbatim; do not paraphrase them into something stronger.
- The circuits are tiny. The novelty is in the kind of statement, not the scale. Say so.
- Submitting code sends it to Harmonic's service. The repository is MIT; the training-data page
  does not say whether submissions are used for training. Nothing here is secret, but do not
  submit anything you would not publish.
- Do not touch `lean/`, `phasegrid/`, `transformer/`, `acas/`, `rnn/` results. New networks (such
  as `FixedPhase12Rom`) go through the existing generators and checks and get their own entries.

## 8. Open questions for Thomas

1. Which proofs in this repository went through Aristotle before the pause, and in what role
   (sorry-filling on your statements, autoformalization, review)? The README line 35 and
   `AUDIT.md` name only Claude Code and Codex; the attribution should be corrected with the scope.
   The kernel checks, `leanchecker` and nanoda replays are unaffected either way.
2. Are there kept Aristotle job logs or returned proof files outside the repository? Worth
   archiving for the write-up and for when Lean comes back.
3. Publish the C and RTL before the artifact question is settled, or hold until it is?
4. Is `FixedPhase12Rom` (workstream 1, option 1) acceptable as a new named network, or should
   workstream 1 stay on `FixedPhase12` with the correction table?

## 9. Files in this packet

| File | What it is |
| --- | --- |
| `START-HERE.md` | one-page plain-English cover sheet |
| `README.md` | this document |
| `research-note-2026-10-27.md` | the research behind sections 1 and 2, with sources |
| `fault_census.py` | measured baselines for workstream 2; usage in its docstring |
| `mechanism_rom_check.py` | the shared-ROM check and the trained/circle/residual split for workstream 1 |
| `runs/` | to be created: one file per Aristotle submission (section 6) |

Scripts need only numpy and run from the repository root.

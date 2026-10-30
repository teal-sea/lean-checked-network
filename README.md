# A trained network, checked by Lean

Small neural networks, with Lean theorems about what they compute on every input in a stated
range. AI coding agents wrote the proofs; Lean's kernel checked them.

![A 113 by 113 square, one cell per input pair (a, b). Each cell is shaded by the proved answer (a + b) mod 113: dark for 0, light for 112. The shade brightens from the top left to the anti-diagonal, snaps back to dark, and brightens again to the bottom right.](transformer/figures/all-pairs.svg)

## What is proved

| Result | Theorem | Scope |
| --- | --- | --- |
| A trained one-layer, four-head transformer adds mod 113 on all 12,769 input pairs | `TransformerBridge.FinalRaw.raw_model_adds_mod_113` | Integer weights at `S = 256`, exact real softmax. Not the float checkpoint |
| ACAS Xu network 1_1 satisfies property 1 on its whole input box | `ACASChecked.acas_1_1_property1` | Exact real arithmetic on TorchLean's semantics. One network, one property |
| For every modulus p ≥ 3, a two-layer network with all ⌊(p−1)/2⌋ frequencies, eight rounded fixed-phase cosine neurons each, adds mod p; at scale 25 the weights fit in 6 signed bits | `PhaseGrid.adds_mod_p_full` | A general proof on Mathlib, not enumeration. The network is constructed, not trained, and grows with p |
| A trained two-layer MLP adds mod 113 on all 12,769 pairs, including the 6,385 it never saw; cut down to one circle wave per neuron, it still does | `LeanCheckedNetwork.Trained.adds_mod_113`, `LeanCheckedNetwork.CircleOnly.adds_mod_113` | Frozen integer weights |
| A trained recurrent network adds binary numbers of every length | `RnnAdder.Trained.adds` | Five reachable states checked, then induction |

No `sorry`. Every theorem uses Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) or fewer.

## What is new, and what is not

- **Transformer.** Brian Naughton's [certified-grokking](https://github.com/brian-naughton/certified-grokking)
  already certifies all 12,769 inputs of the same architecture, with a trusted Python interval
  core. Gross, Kwa and Agrawal (2023) have brute-force Coq proofs of accuracy for trained
  max-of-two transformers, in floats. Here the whole chain, softmax included, is closed in
  Lean's kernel.
- **ACAS Xu.** TorchLean already supplies exact network semantics and the local alpha-CROWN rules;
  Marabou proofs are already checked in Imandra; lean4-mlir (Koonce, 2026) already has
  kernel-checked CROWN-IBP certificates for an MNIST network. This project proves the receipt
  checks and the complete input-tree composition around TorchLean's semantics, for one
  alpha-beta-CROWN tree. No novelty claim is made.
- **Every modulus.** Gromov (2023) gave analytic weights whose random phases cancel the unwanted
  waves only on average. Fixing the phases on a grid makes the cancellation exact, and the
  result holds for every modulus.

Full prior work: [RESULTS.md](RESULTS.md#prior-work-and-what-is-new-here) and
[acas/README.md](acas/README.md#prior-work).

## Two things worth taking from it

**Pack, then check.** Proving the transformer's lookup tables equal the products of its weight
matrices one slot at a time cost about 370 seconds per slot (measured on five), or about 94
hours for all 916 (derived, never run). Writing each row as the digits of one large integer and
checking whole attention heads took 200 seconds to compile and 322 to replay. The method is in
[transformer/mathlib/KRONECKER.md](transformer/mathlib/KRONECKER.md).

**Checking still costs far more than finding.** For ACAS Xu 1_1, alpha-beta-CROWN found its
34-leaf proof in 16 seconds. In a pre-release run, compiling the Lean check of all 34 leaves'
arithmetic took 38 minutes (about 3.5 CPU-hours), and replaying it about 2.8 CPU-hours more.
For the release, compiling and replaying the new modules took about 11.8 CPU-hours.

## Limits

- Tiny models on toy tasks. The transformer and MLP proofs go through every input, which does
  not scale to large models.
- The proved objects are integer or exact-real models, not floating-point execution.
- The transformer check replays the shipped compiled objects. Rebuilding the whole bundle from
  source has not been shown: one module rebuilt from source compiled but gave different bytes.
  [VERIFY.md](VERIFY.md) states exactly what a replay assumes.
- The ACAS Xu importer, from ONNX to Lean, is audited and hash-pinned but not proved. Nothing
  here is a claim about aircraft.
- Review was by AI agents, not outside people. [AUDIT.md](AUDIT.md) lists what they found and
  what changed.

## Check it yourself

| What | How |
| --- | --- |
| Transformer | The command block in [VERIFY.md](VERIFY.md), which also states what a replay does and does not establish. Needs 16 GiB of memory and 30 GB of disk |
| MLP, circle-only, FixedPhase12/16, Mod12All | `./run_lean.sh`, under 1.5 hours on 4 cores. CI runs it on every pull request and push to main |
| Mod257Min | `./run_lean_fixed_phase.sh`, not in CI |
| ACAS Xu | `cd acas && ./recheck.sh`; see [acas/README.md](acas/README.md) |
| Every-modulus theorem | [phasegrid/README.md](phasegrid/README.md) |

## How it was built

AI coding agents (Claude Code and Codex) wrote the proofs, generators and checks. Thomas Lince
chose the problems and checked the frozen statements, limits and releases by hand; he did not
write the proof terms. Reviewing agents attacked the statements, the trust base and the claims
twice, on 2026-10-15 and 2026-10-25.

## Where the details are

| | |
| --- | --- |
| [RESULTS.md](RESULTS.md) | Every result with how it was established, the MLP method, reproduction and history |
| [MECHANISM.md](MECHANISM.md) | The circle explanation as an exact certificate, in Python |
| [transformer/STATUS.md](transformer/STATUS.md) | The transformer proof, piece by piece |
| [acas/README.md](acas/README.md), [acas/STATUS.md](acas/STATUS.md) | The ACAS Xu theorem, its gates and costs |
| [phasegrid/](phasegrid/README.md), [rnn/](rnn/README.md), [sweep/](sweep/README.md), [prime_env/](prime_env/lean_mod_add_proof/README.md) | The every-modulus theorem, the recurrent adder, the training-run sweep, a Prime Intellect environment graded by the kernel |

MIT licence. To cite, use [CITATION.cff](CITATION.cff).

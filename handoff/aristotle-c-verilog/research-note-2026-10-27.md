# Aristotle for C and Verilog: what it means for lean-checked-network

Research note, 2026-10-27. Sources at the end. Status words follow the repository's house rule:
what Harmonic states on its own pages is marked **vendor**; what a third party reported is marked
**reported**; what was computed here from the repository is marked **measured**.

## 1. What was announced

- **Vendor.** Harmonic's news post of 2026-10-27, "Aristotle Expands Into Formal Verification for
  Software and Hardware, Starting With C and Verilog": Aristotle "proposes properties from your code,
  then reports which ones it proved, which it didn't," and "the assumptions each proof rests on."
  For C: "functional correctness and the absence of certain classes of undefined behavior."
  For Verilog: "total logical verification across control-path properties such as liveness and
  safety" plus "mathematical data-path properties." Workflow: review the proposed properties, commit
  them to the repository, run Aristotle in CI on every commit. "Available today", "self-serve,
  consumption-based pricing", enterprise plans with on-prem or private-cloud deployment.
- **Vendor.** Product page (harmonic.fun/aristotle): "No spec is required." Properties are written in
  plain English or proposed by Aristotle. Verdict per property: proved, refuted (with explanation),
  or left open. "Every proof is machine-checked." The checker is not named anywhere public. Lean is
  not mentioned on the product page at all.
- **Vendor case studies.**
  - LibTomMath 1.2.0 (C): fast squaring and Montgomery reduction, plus a comparison helper. Two bugs
    found (missing size checks allowing an out-of-bounds stack write on oversized direct calls; a
    pointer formed before the start of an array when comparing equal numbers). Repaired code proved
    against specifications "for results, memory safety, errors, and stored values"; optimized code
    re-proved against the same specifications; modular exponentiation 31 to 38 percent faster
    (benchmarked, not proved). Stated assumptions: x86-64, 60-bit digits, 128-bit intermediates,
    caller-owned initialized buffers, standard realloc, callers meet obligations. Termination and
    the rest of the library are not proved.
  - Tensordyne (Verilog): one block of 12.2M gate equivalents, 1.24M flops, 45 Mbit SRAM, 312 pages
    of spec. 241 properties (100 written by Aristotle from the specs, 141 pre-existing RTL
    assertions): 185 proved, 56 refuted with reproducible counterexamples, bugs 25,000 to 110,000
    cycles after reset. "No cycle bound" on the proofs. A second project wrote RTL from spec, derived
    and proved 37 properties, then optimized power and area about 20 percent with re-proof.
  - DIII-D testimonial (Mitchell Clark): a plasma-control algorithm reproduced from one paper and a
    254-word prompt in four hours; Aristotle "verified the C code's safety, and generated equivalent
    Verilog."
- **Reported.** Reuters (via syndication, 2026-10-27): the expansion, the DIII-D claim, PHP bugs found
  with "the technology", $120M Series C at $1.45B (Nov 2025). No technical detail.
- **The Lean pause.** The only source is the email you received. Nothing public mentions it as of
  this afternoon: not Harmonic's news page, not the product page, not the Reuters coverage, and no
  indexed Zulip or forum thread. Treat it as real (it is a first-party email) but undocumented.

## 2. What is underneath the C and Verilog flows: the evidence

The public pages never name the proof checker. Circumstantial evidence that Lean 4 is the
substrate, at least for hardware:

- Satnam Singh (Harmonic, ex-Google/Groq hardware formal verification) posted a hiring call for people
  with "industrial experience of formally verifying hardware" to "help to develop a flow based on the
  Lean theorem prover" (X, late 2025, **reported** via search snippet).
- His Cambridge seminar (2026-02-26) and Imperial talk (2026-05-05): circuits described in Ruby
  (Jones and Sheeran's relational HDL) "implemented in Lean 4 as an embedded domain specific
  language", properties proved by Aristotle, "machine-checked by the Lean 4 interactive theorem
  prover". Slides mention that "Aristotle has MathLib" for numerical properties of circuit outputs.
- Harmonic's code-verification track record is Lean: the Dec 2025 result is 96.8 percent on VERINA, a
  Lean 4 benchmark (proof generation with the reference algorithm supplied, per Logos Research).
- Third parties using Aristotle for software verification go through Lean: Runtime Verification's
  Linux UVC parser work (C rewritten in Rust, extracted via Charon/Aeneas into Lean 4, obligations
  closed by Aristotle and Aleph, "every proof is checked by the Lean kernel"); the Ethereum zkEVM
  Rust-to-Lean experience report (CAV 2026 AIMACS workshop), same shape.

Evidence pointing the other way, or at a hybrid:

- The Tensordyne numbers (1.24M flops, unbounded proofs, counterexamples 110,000 cycles deep, 241
  properties) are the profile of an industrial model checker (IC3/k-induction class), not of kernel
  proof terms over RTL at that scale. A plausible architecture is a model-checking engine for RTL
  with Lean used for data-path mathematics, or a certified pipeline, but Harmonic has not said.
- The C claims ("absence of certain classes of undefined behavior", platform assumptions about
  60-bit digits and 128-bit intermediates) read like a C semantics with an explicit memory and
  integer model. Whether that semantics lives in Lean, in an SMT-backed tool, or both is not public.

Conclusion: assume nothing about replayability until tested. The one question that decides whether
this fits this repository is: **does the product export a proof artifact that an independent checker
can replay, with the axioms and assumptions printed?** If it exports Lean objects, it slots into the
existing `leanchecker` / nanoda discipline. If it exports only a verdict and a report, a result from
it can only be labelled as a third-party tool verdict, a weaker class than anything currently in the
README.

## 3. What this means for this project

### 3a. The Lean pause: correction. Aristotle was used heavily, off the record

- Thomas reports heavy Aristotle use on this project. The repository carries no trace of it: no
  mention in any source, doc, script, log or commit message, and the README's "How this was built"
  names only Claude Code and Codex. Two consequences. First, the pause removes a working part of the
  proof pipeline, so which proofs went through Aristotle needs to be known before the open items are
  scheduled. Second, the attribution text in README.md (line 35) and the audit's authorship
  statement are incomplete and should name Aristotle, with the scope of what it filled, since the
  trust story leans on stating who produced the proof terms. The kernel checks are unaffected
  either way: `leanchecker` and nanoda replay the objects regardless of who wrote them.
- The one place a strong external Lean prover would have helped is the open mathematics: the circle
  certificate "not yet in Lean" (MECHANISM.md), the three statements in `phasegrid/.../Open.lean`,
  the loose scale bound (M = 24 proved, M = 2 observed), and the link between the p = 113 tables and
  the every-modulus theorem. Those are genuine Mathlib proofs about trigonometric sums and error
  bounds, the kind of thing Aristotle was good at. That route is paused.
- Alternatives for that class of work, as of today: Aleph Prover (Logical Intelligence) is still
  invite-only per its own site; AxiomProver is not public, although Axiom's AXLE Lean service is
  free (it is infrastructure, not a prover); Math Inc's OpenGauss is an MIT-licensed orchestrator
  that drives Claude Code or Codex through lean4-skills, so it is the same class of agent the
  project already uses; open-weights provers (Goedel-Prover-V2, DeepSeek-Prover-V2, Kimina) are
  competition-math models and have not been shown to do project-scale engineering proofs.
- `prime_env/` becomes slightly more relevant, not less: with the main commercial Lean prover paused,
  open provers and the RL environments that train them matter more.

### 3b. C and Verilog are the missing layer of this project's own story

The README says the frozen weights are "the form a phone chip would run", yet the repository contains
no C and no Verilog. Everything proved is about the mathematical integer object. Aristotle's new
product is aimed precisely at the next layer: is the code or the RTL that runs this object right?

**Measured** here from `network/*.npz`, worst-case bounds for a straightforward C port
(`hidden = (E1[a]+E2[b])^2`, `score[c] = sum_h W2[c][h]*hidden[h]`, first-index argmax):

| network | p | H | max |weight| | hidden entry bound | per-term bound | score bound | int32 ok | observed min margin |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | ---: |
| trained (128 neurons) | 113 | 128 | 127 | 64,516 | 8,193,532 | 1,048,772,096 | yes | 32,654,491 |
| circle-only | 113 | 128 | 130 | 67,600 | 7,909,200 | 1,012,377,600 | yes | 1,980,696 |
| FixedPhase12 | 113 | 12 | 127 | 64,516 | 8,193,532 | 98,322,384 | yes | 1,021,168 |
| FixedPhase16 | 113 | 16 | 127 | 64,516 | 8,193,532 | 131,096,512 | yes | 1,416,180 |
| Mod12All | 12 | 40 | 25 | 2,500 | 62,500 | 2,500,000 | yes | 308,750 |
| Mod257Min | 257 | 12 | 127 | 64,516 | 8,193,532 | 98,322,384 | yes | 375,872 |

Every network fits 32-bit signed accumulators with proof-friendly headroom (the 128-neuron score
bound is about half of 2^31; hidden entries need 32 bits, not 16). So a C implementation has a clean,
provable "no signed overflow, no out-of-bounds, no UB" story, which is exactly the C property class
Harmonic advertises. The functional spec already exists: `LeanCheckedNetwork.answer` in
`Network.lean`, plus the kernel-checked `adds_mod_113` theorems. If the C flow is Lean-based, the
property "the C function equals `answer E1 E2 W2 a b` for all a, b < 113" composes with the existing
theorem into an end-to-end statement about the binary's semantics. If it is not Lean-based, the
property has to be restated in Harmonic's language, and the link to the kernel-checked theorem is a
human-checked correspondence, to be labelled as such.

For Verilog, `FixedPhase12` (12 neurons, 8-bit weights, 113 classes) is the natural first target:
two 113 x 12 x 8-bit ROMs, 12 adders, 12 squarers (17 bits), 113 twelve-term dot products (27-bit
signed), a 113-way argmax with the first-index tie rule. The property is a pure data-path statement
over 12,769 input pairs. Any formal tool can close it; the value of running it through Aristotle is
to learn what artifact comes back, not whether the circuit is right. `Mod257Min` is the same at
66,049 pairs if a larger case is wanted.

Not good first targets: the transformer (the packed integer program works with numbers near 2^200,
so a C port needs bignum arithmetic and the "no UB" story becomes a library-correctness story), and
ACAS Xu (the theorem is over exact reals and explicitly excludes IEEE floats; relating a float C
implementation to it is a research project, not a credit-sized experiment).

### 3c. A concrete, bounded experiment for the $500 before Nov 27

1. Write `c/mlp_mod.c`: one generic function over `(p, H, E1, E2, W2)` tables with int32 accumulators,
   plus generated header files from `network/fixed12.npz` and `network/trained.npz` (reuse
   `gen_lean.py`'s reading code). Add a Python differential test against the Lean weight files and
   `verify_weights.py` so the C port is pinned to the same bytes as the proofs.
2. Submit to Aristotle's C flow with two property sets: (a) the properties it proposes on its own
   (this measures what it thinks matters); (b) the two you care about, written in plain English:
   no undefined behavior for all a, b < p, and output equals `(a + b) mod p` for all a, b < p.
3. Record, verbatim, what comes back: the verdict per property, the assumptions list, whether a
   proof artifact is downloadable, in what format, and whether it can be replayed independently.
   That record answers the only question that matters for this repository's evidence standard.
4. If an artifact is exportable and Lean-based: add a `c/STATUS.md` in the house style and state the
   composed theorem honestly, including the C semantics assumptions Harmonic lists.
   If not: still worth one line in the README's prior-work or limits section, labelled as a
   third-party tool verdict without an independently replayable artifact.
5. Repeat for `verilog/fixedphase12.v` with the single data-path property. Same recording.
6. Optional, if credits remain: feed Aristotle the C port of the 128-neuron trained network and ask
   it to propose and prove properties without being told the answer. Compare what it proposes with
   the README's claims. That is a cheap external check on whether the stated properties are the
   ones a verifier would find natural.

Budget note: Harmonic publishes no price list; the credits are consumption-based. Run the 12-neuron
cases first and watch the balance before the 128-neuron one.

### 3d. Positioning

- Harmonic's move validates the direction this project took: machine-checked statements about the
  deployed artifact, not just about the mathematics. The gap this repository already documents
  (integer object proved; float checkpoint and silicon not) is now the gap a funded company is
  selling tools for.
- A verified C or Verilog layer would make this the first public example, as far as this search
  found, of one trained network with a kernel-checked correctness theorem, a verified C
  implementation of the same integer object, and a verified RTL implementation, with every trust
  boundary named. No search result today shows anyone with that chain for a neural network.
- The repository could also serve as a benchmark for code-verification provers the way `prime_env`
  does for Lean provers: "prove this inference routine equals this spec" at many (p, H). VERINA
  has 189 tasks and is already near saturation; this would be a different, structured family.

## 4. Caveats on the evidence

- Everything about the product's internals is inferred. Harmonic names no checker, no spec language
  and no proof format on any public page found today.
- The case studies and the DIII-D quote are vendor material. The Reuters piece adds no independent
  technical confirmation.
- Whether submitted code is used for training is not stated on the training-data page. For an MIT
  repository this is a minor concern, but check the terms before submitting anything you would not
  publish anyway.
- The Lean pause has a single source: the email.

## Sources

- https://harmonic.fun/news/aristotle-software-hardware-verification/
- https://www.harmonic.fun/aristotle/
- https://www.harmonic.fun/aristotle/case-studies/libtommath/
- https://www.harmonic.fun/aristotle/case-studies/tensordyne/
- https://harmonic.fun/news
- https://www.harmonic.fun/news/verina-benchmark/
- https://www.harmonic.fun/legal/training-data-summary/
- https://kelo.com/2026/10/27/robinhood-ceos-ai-startup-harmonic-expands-into-software-chip-design-verification/
- https://www.whalesbook.com/news/English/technology/Harmonic-Expands-AI-Verification-to-Chip-Design/6ae0d6534fc30694db4f0729
- https://news.ycombinator.com/item?id=46561569
- https://www.cst.cam.ac.uk/seminars/list/243940
- https://satnam6502.github.io/
- https://x.com/satnam6502/status/1994094137386344665
- https://runtimeverification.com/blog/hardening-linux-c-code-a-rewrite-and-verify-loop
- https://arxiv.org/abs/2605.30106
- https://eco.com/support/en/articles/14114345-what-is-the-harmonic-aristotle-api-formal-verification-ai-for-developers
- https://www.logosresearch.ai/blog/verina-state-of-the-art-verified-code-synthesis/
- https://logicalintelligence.com/aleph-prover.html
- https://axle.axiommath.ai/
- https://github.com/math-inc/OpenGauss
- https://arxiv.org/html/2603.02668 (SorryDB, on open provers)

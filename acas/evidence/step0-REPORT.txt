# Step 0: frozen contract

Status: **completed for gate review**. The statement, exact importer, arithmetic profile and local
proofs, and certificate-format draft are present. The final validation passed. No Step 1 leaf replay,
checker implementation, safety proof, nanoda run, download, network write or upstream edit was performed.
The Scholar gate review is still required; this report does not grant that approval.

Numbers in code/specification examples are **derived exact constants** unless identified as source
literals. SHA values and validation outcomes below are **measured**. Source decimal tokens are
**reported (source: the copied prop_1.vnnlib)**, with byte-exact agreement **measured** by importer.py.
The first working report was written before implementation, within the requested draft deadline.

## Frozen real statement

[Spec.lean](Spec.lean) defines `Frozen.ACASXu_1_1_Property1 : Prop`, with no proof:
for every real input tensor in the closed componentwise box, output coordinate Y_0 of
`Frozen.network.model.forward` is strictly below the exact decimal threshold.

| Coordinate | Lower source token | Upper source token | Derived exact real fractions, lower / upper |
|---|---|---|---|
| X_0 | `0.6` | `0.679857769` | `3/5`, `679857769/1000000000` |
| X_1 | `-0.5` | `0.5` | `-1/2`, `1/2` |
| X_2 | `-0.5` | `0.5` | `-1/2`, `1/2` |
| X_3 | `0.45` | `0.5` | `9/20`, `1/2` |
| X_4 | `-0.5` | `-0.45` | `-1/2`, `-9/20` |

Source threshold: `3.991125645861615`; derived exact fraction:
`3991125645861615/1000000000000000`. The VNNLIB unsafe assertion is `Y_0 >= threshold`,
so the frozen safety claim is **strict** `<`, including the box boundary.
All bound assertions, variable names, directions and decimal byte tokens match exactly;
the importer also rejects additional assertions and altered source bytes.

Measured source SHA256:

- [ACASXU_run2a_1_1_batch_2000.onnx](ACASXU_run2a_1_1_batch_2000.onnx):
  `843f7110bf5a8b7f0eeb9b1c548d9d558db9099328b392423d5a7444a0656dd4` — matches W1's recorded fingerprint.
- [prop_1.vnnlib](prop_1.vnnlib):
  `7a9a9930711817c6cc39940f5c1d0f8c51f2ed82f38e203c4b5de03c19bd4ced`.

The statement uses existing TorchLean `CROWNQuery.Network.model` real module semantics.
No new dense-network semantics was necessary. The alpha tensors in Net.lean are zero placeholders
ignored by `Network.model`; this is not a restriction on later certificate alpha choices.
The expected weights/property remain fixed independently of those choices.

## Import contract and agreement

[IMPORT.md](IMPORT.md) documents the decoder and normalization boundary. Measured graph:
ONNX IR version 3, default opset 8; zero Sub; Flatten(axis=1); six MatMul/Add/Relu blocks;
final MatMul/Add. Matrix shapes in original [in,out] order are [5,50], five [50,50], [50,5].
Generation transposes to TorchLean's [out,in] convention. Derived totals from those measured
shapes: 13000 weights and 305 biases. All input_AvgImg values are exactly zero. There is no
input scaling Div or output transform; the property already uses normalized coordinates.
The initializer graph-input declarations cannot override our fixed constants.

The importer is stdlib-only, reads IEEE float32 bit fields directly into exact Fraction values,
rejects nonfinite/unsupported encodings and unsupported operators/wiring/shapes, and pins the
full source hashes before generation. It emits Net.lean, Spec.lean, the agreement fixture and manifest.
Initializer bit hashes are retained. Signed zero has the same real value, with source distinction
preserved by hashes. ONNX-to-constant correspondence is audited, not proved.

Measured: **20 distinct exact rational inputs, all 5 outputs per input agree exactly** with the
stdlib-Python forward pass; **100 scalar equalities** is derived from those measured dimensions.
Inputs include both box corners and its midpoint, plus deterministic mixed-coordinate points.
Python multiplies the original [in,out] matrices, independently of the Lean transpose.
Full exact vectors are in [agreement.json](agreement.json); [Agreement.log](Agreement.log) has
exactly the measured 20 `true` results. These concrete checks use `#eval` and are audit evidence,
not kernel-reduced safety proofs. [Bridge.lean](Bridge.lean) separately proves the generic
`Frozen.evalQ_real` embedding into the frozen real network semantics, with standard axioms only.

Measured: all **11 importer tests passed** ([importer-tests.log](importer-tests.log)). Controls cover
all original float32 bits against an independent struct/Fraction conversion, extreme/subnormal/signed-zero
encodings, nonfinite rejection, tensor-size mismatch, unsupported Tanh, broken wiring, changed property
decimals, extra assertions, wrong source hashes, exact tokens, and distinctness of test inputs.
Some tests exercise multiple cases; the test-method count is not a count of scalar checks.

## Local arithmetic proofs and format decisions

[PROFILE.md](PROFILE.md) freezes a parametric dyadic scale, positive divisors, signed Euclidean floor
and ceiling, interval coefficient/bias invariants, four-corner multiplication, rounding-error flow,
ReLU stable cases/lower line/upper secant, and intersection only between previously proved enclosures.
[Rounding.lean](Rounding.lean) proves the requested local lemmas, including a bridge from the executable
integer grid-rounding rule to real rational bounds and strict single-grid-step error bounds.
Measured: **20 local lemmas compile**. A whole affine loop and tree-coverage theorem remain future
checker work, as in the plan. No global property proof is claimed.

[FORMAT-v0.md](FORMAT-v0.md) specifies exact root containment and shared closed cuts; complete tree
traversal; rejection of missing/reused/unreachable nodes; target/side/layer/neuron slope indexing;
range and shape checks; ordered optional proposals; and rejection of beta, cutting planes and activation
splits. Axis-aligned input-tree cuts are supported. Chosen rational encoding: canonical reduced
integer/positive-denominator pairs. Chosen omitted-slope default: zero; partial/duplicate blocks reject.
This avoids ambiguous fallback lookup while admitting alternative valid choices.

The four required test classes have concrete examples: wrong input; malformed/out-of-range hint;
false property with exact counterexample; valid alternative hint. They include threshold equality,
shared split boundaries, signed negative division/product, crossing-zero coefficient intervals and
positive/negative/zero margins at an exact tiny scale. These are future checker test requirements,
not a claim that a checker exists. [ArithmeticExamples.lean](ArithmeticExamples.lean) additionally
kernel-checks four exact arithmetic fixtures used in those examples (measured pass).

## Compilation and resource evidence

Measured environment: Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
TorchLean `a207636b40f1076981994b4a28e272a9bdc71750`;
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The own Lake project declares a path dependency. [lean.sh](lean.sh) directly reuses the existing
built module paths, so validation does not update the read-only dependency or rebuild Mathlib.

Final validation ran sequentially in `cert-step0-validation.service`, measured exit status zero,
with configured MemoryMax 24 GiB and CPUQuota 600%, six-core affinity and six Lean threads.
Initial and final df availability both displayed 93G (measured rounded display), above the required
45 GB reserve. Each module also has a timeout; all finished below the long-job threshold.
These are compilation/import-audit measurements, **not Step 1 checker-performance measurements**.

| Module | Measured outcome | CPU seconds (derived sum of measured user + system) | Measured peak RSS KiB |
|---|---|---:|---:|
| Net | pass | 65.74 | 4,540,380 |
| Spec | pass | 4.01 | 3,785,144 |
| Rounding | pass | 9.12 | 6,789,376 |
| Bridge | pass | 4.52 | 3,795,900 |
| ArithmeticExamples | pass | 7.27 | 6,746,912 |
| Agreement | pass | 8.54 | 3,813,180 |

Commands: `./validate.sh` reproduces generation, tests, compilation, axiom and agreement audits using
the installed dependencies. Run it under the same systemd resource limits as the recorded final run.
[validation.json](validation.json), module `.log`/`.time` files and [runs.jsonl](runs.jsonl) retain evidence.
No `sorry`, custom axiom or native proof acceptance is present in the delivered Lean sources.

Measured axiom outputs from the final compile:

```text
'Profile.floorDiv_bounds' depends on axioms: [propext]
'Profile.ceilDiv_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.scale_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.down_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.le_up' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.down_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.up_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.floorDiv_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.ceilDiv_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.relu_interval' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.relu_inactive' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.relu_active' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.integer_rounding' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.mul_between' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.product_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.rounded_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.rounded_product' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.relu_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.relu_secant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.intersection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Frozen.evalQ_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.negative_division_fixture' does not depend on any axioms
'Profile.negative_grid_product_fixture' does not depend on any axioms
'Profile.crossing_zero_fixture' depends on axioms: [propext, Classical.choice, Quot.sound]
'Profile.strict_threshold_fixture' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Artifact fingerprints

Each path is relative to this Step 0 directory. SHA256 values below are measured.
[SHA256SUMS](SHA256SUMS) also covers input bytes, build scripts and toolchain declaration.
The report itself is excluded to avoid a self-referential digest.

| Artifact | SHA256 |
|---|---|
| [Spec.lean](Spec.lean) | `fc9a750a19646c2e66ced81bb8138620861b4c01e1fd0cd9b85baf1030e1a9b0` |
| [Net.lean](Net.lean) | `4f89de9f7ca25762b638c97a51625d0c1065a0d3b5ab2ffe5de3ba7f32964426` |
| [importer.py](importer.py) | `115e6d183269e926882ffe580693ca4936ac02bf1feb2fd27c87c029da578a83` |
| [PROFILE.md](PROFILE.md) | `79bfa27f7dfcefcf5d29a22ff950cda6760c4ea76ec8af65e4970d5cd68222d2` |
| [Rounding.lean](Rounding.lean) | `384b6c00792017043c4ebeaf0c95ceebaa4c3265becd97d4a426afd5edffb5d0` |
| [FORMAT-v0.md](FORMAT-v0.md) | `347e9ebdd9b9c3cd438bd2557725b7dc78819e9860c988243f94f6cb6401e254` |
| [IMPORT.md](IMPORT.md) | `1693027a59aea54341ef41201a67f7028c62fe065caac3c8ea2ab47ee30ca5cc` |
| [Bridge.lean](Bridge.lean) | `cdb9f9d6f742ee1be7e1c0cd666559b5574d64929c8272e9c63a304abbb20d08` |
| [Agreement.lean](Agreement.lean) | `3a314cf02d203827e597287dee4e55a3d781363a8b7f5d680866bb8f134936d8` |
| [ArithmeticExamples.lean](ArithmeticExamples.lean) | `8aff65fec1aa9729eff890b0245068edc391c2cf504c8521a08b9ac5461f8ed6` |
| [test_importer.py](test_importer.py) | `cbde587b38dd65c3014cfea6099f0f9e6fc894e514cbb697eb7465d2120ddfd0` |
| [manifest.json](manifest.json) | `d77f409d7ecab7df58bd762d9f015d6e6b672444c61864569c15202008b2cb57` |
| [agreement.json](agreement.json) | `b3ae3c9c331009f8a8b9e9afba7c68e3be4c1d1f985cb1d0c9106668205df2bd` |
| [validation.json](validation.json) | `92d122e9f47697ca802be17157cebe198fdcafd41226a90978a6ce9d56c3ce88` |

## Gate-review questions and remaining boundaries

- Scholar should review the byte-to-rational decoder, transpose, normalization removal and strict
  property direction. No importer-correctness theorem is claimed; this is the explicitly audited boundary.
- Confirm the format's canonical rational encoding and omitted-slope default before a converter is written.
  A later algorithm profile must enumerate exactly which slope targets it consumes, with unused keys rejected.
- Tree coverage and full affine/checker composition are specified here and require the later soundness proof.
  The local arithmetic lemmas do not imply that a supplied intermediate bound is trustworthy.
- No code blocker was found in Step 0. The external review gate remains open; no later step was started.
  IEEE float32 execution, nanoda replay of an eventual safety theorem, and aircraft claims remain outside
  this delivered statement and validation.

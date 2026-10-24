# Step 1: real-leaf kernel cost — stopped at the gates

**No candidate cleared the first-leaf gate. Do not start a large Step 2 soundness proof on the strength of these measurements.** TorchLean forward replay and the monolithic fixed-grid backward replay exhausted their per-unit memory caps. Splitting backward checks into declarations reduced the observed memory growth, but the unfinished weakest-leaf run already exceeded the conservative full-tree CPU projection gate. No unconditional real safety theorem, completed whole-leaf kernel acceptance, full-tree proof, export or nanoda replay is claimed.

Plain answer: **this work does not establish that Lean's kernel can check the real complete proof within the prescribed budget.** Its arithmetic can be replayed exactly in compiled Lean, and individual real target computations kernel-check, but the tested whole-leaf drivers do not meet the gates. **Step 2 should be deferred.** A separately scoped process-batched or checked-product/linear-witness cost pilot is needed before choosing what to prove. Those alternatives are unmeasured here.

All performance quantities in tables are **measured** unless explicitly labelled **derived** or **reported (source)**. Layer, node, profile and format numbers are identifiers; mathematical constants are **derived exact**. OOM and stopped runs are censored, never successful timings. First REPORT.md draft was written before experiments, within the requested deadline; this final report replaces it in place.

## Gate edits and local proofs

- [FORMAT-v0.1.md](FORMAT-v0.1.md): inherits frozen v0, specifies concrete UTF-8 JSON; canonical integer-string grammar `0|-?[1-9][0-9]*`; rational wire examples `["0","1"]`, `["-1","2"]`; zero-based array-position node identity; exact dense block dimensions, targets, sides, dependency order and missing-whole-block zero expansion; partial/extra/unused blocks reject. The forward profile has a single vector per ReLU. Upper objective conventions are explicit. No general wire parser is claimed.
- [PROFILE-v0.1.md](PROFILE-v0.1.md): relational invariant lowerForm(x) <= target(x) <= upperForm(x); coefficient intervals enclose relaxed forms, not an alleged affine equality with the nonlinear network. Positive coefficients preserve lower/upper line order, negative coefficients reverse it, uncertain signs require decomposition or enclosure.
- [SignedSubstitution.lean](SignedSubstitution.lean): signed substitution and positive/negative decomposition, plus negative and crossing-zero ReLU coefficient fixtures. Measured axiom closure of every declaration: `[propext, Classical.choice, Quot.sound]` ([signed-audit.log](signed-audit.log)). [IntControls.lean](IntControls.lean) additionally kernel-checks the executable negative and crossing-zero branches, with `[propext]`.
- [Rounding.lean](Rounding.lean) is copied unchanged from Step 0. Final resource-compliant repeat: [rounding-final-audit.log](rounding-final-audit.log). Whole-loop relational induction and coverage-to-safety composition remain Step 2 work.

The main clarifications/local lemma were completed before the forward pilot; backward and checkpoint specializations were declared before their respective leaf runs. Frozen Step 0 files and upstream checkouts were not modified.

## Exact inputs and arithmetic boundary

Measured input fingerprints:

| Input | SHA256 |
|---|---|
| producer `cert-supported-crown-1_1-p1.json` | `89d8742b8a08f2259dfb99f8dcac061cad9276db1fb75fb2d5a896ed89cc0b0f` |
| frozen copied Net.lean | `4f89de9f7ca25762b638c97a51625d0c1065a0d3b5ab2ffe5de3ba7f32964426` |
| frozen copied Spec.lean | `fc9a750a19646c2e66ced81bb8138620861b4c01e1fd0cd9b85baf1030e1a9b0` |
| ONNX | `843f7110bf5a8b7f0eeb9b1c548d9d558db9099328b392423d5a7444a0656dd4` (reported: Step 0; parameter agreement rechecked here) |
| VNNLIB | `7a9a9930711817c6cc39940f5c1d0f8c51f2ed82f38e203c4b5de03c19bd4ced` (reported: Step 0) |

Source certificate schema is `restricted-acas-box-v1`; the pilot algorithm profiles are separately versioned in FORMAT-v0.1.md. [convert_forward.py](convert_forward.py) emits every terminal as a TorchLean Query, using frozen Net.lean, exact binary-rational leaf boxes, exact decimal threshold and all-zero legal ReLU slopes. The input source and network hashes are pinned. [input-audit.json](input-audit.json) records exact tree validation by the copied independent Python routine and byte equality of the frozen network. Measured terminal/generated-query count: **34**. Weakest-margin node is **38**, selected from W2b results before running; the next selected nodes are **32, 40, 8**.

[convert_int.py](convert_int.py) checks every producer weight and bias against exact literals in frozen Net.lean before generation. Precision is **2^-50** (derived exact grid), and all imported weights, biases and binary leaf endpoints must be exactly representable. Final comparison uses exact decimal **3991125645861615/1000000000000000**, never a rounded threshold. Forward uses direct upper Y_0-T; backward derives a lower bound for -Y_0 and compares it with -T. The producer cannot substitute the network or property. Import correspondence is audited, not proved; real-valued exact-parameter semantics are intended, not IEEE inference or aircraft safety.

Profiles exercised: `torchlean-forward-v0.1`; `int-backward-adaptive-v0.1`; `int-backward-checkedbounds-v0.1`. The latter carries an untrusted intermediate table, but each endpoint must equal a recomputed backward/IBP intersection from strictly earlier layers. It is not acceptance of supplied bounds by assertion.

## Kernel pilots and gates

| Candidate / node 38 | Wall s | CPU s | Peak RSS KiB | Outcome |
|---|---:|---:|---:|---|
| Forward initial run, extra virtual-address cap | 63.80 | 57.42 | 9905840 | SIGABRT / bad_alloc; superseded by cgroup-only retry |
| Forward cgroup-only retry | 275.96707 | 133.612233 | not found | systemd OOM-kill at MemoryMax 16 GiB |
| Monolithic Int backward | 591.16 | 582.98 | 18186736 | OOM-kill; no completed leaf theorem |
| Checkpoint Int, separate declarations in one module | 728.96 | 1422.52 | 17704936 | deliberately SIGTERM-stopped at CPU projection gate; unfinished |
| One deep local target, affine layer 5 / neuron 0 | 12.90 | 12.78 | 2677856 | kernel equality passes; not whole-leaf acceptance |

The forward cgroup-only retry's GNU time process was stopped with its unit, so its exact peak RSS is unavailable. Last sampled cgroup peak was **16909205504 bytes**, a measured lower bound; sampled process RSS was at least **18933688 KiB**. Process RSS includes shared imported mappings and can exceed cgroup-charged memory. The monolithic OOM is explicitly recorded in [int38-kernel-unit.log](int38-kernel-unit.log); the checkpoint stop is a cost-gate stop, not reported as an OOM. Raw times, unit outcomes and [resource-samples.jsonl](resource-samples.jsonl) retain the distinction.

**1a gate: stop.** Measured retained rational bit maxima (numerator / denominator) were affine0 24/36, ReLU0 102/105, affine1 559/561, ReLU1 1087/1087, affine2 5280/5288, ReLU2 11103/11103, affine3 134946/134942, ReLU3 269299/269297. These are compiled #eval measurements of retained coefficients/biases, not transient gcd operands ([forward-trace-progress.txt](forward-trace-progress.txt)). The compiled full query timed out after **900.29 s wall / 828.18 CPU s**; the stage trace after **900.26 s wall / 746.32 CPU s**. Final forward margin is **not found**. Classification: rational growth/resource failure, not demonstrated relaxation insufficiency. No disagreement with the backward Python proof is claimed. Four forward leaves were not attempted.

[ForwardAudit.lean](ForwardAudit.lean) kernel-checks only the conditional `query.check = true -> query.Safe` via TorchLean Query.check_sound, with standard axioms. Its antecedent was not proved. Forward data compilation cost **67.38 CPU s** for Net and **4.21 CPU s** for node input; the conditional audit cost **4.44 CPU s**.

**Monolithic 1b gate: stop for memory.** Its compiled replay and all intermediate comparisons pass, but its kernel reduction does not complete within the cgroup cap. Four monolithic leaves were not run.

**Checkpoint 1b gate: stop for cost.** At stop, the incomplete run already costs **1422.52 CPU s**. The conservative uniform projection is **13.4349 CPU-hours** (derived: partial cost times 34), excluding the unfinished remainder and every additional overhead. That exceeds the **12 CPU-hour gate** (reported: brief). This is a projection model, not a lower bound on every other leaf's actual runtime. A W2b operation-count-weighted sensitivity uses **173039161 / 5945017 = 29.106588 equivalent weak leaves** (derived from reported W2b per-leaf counts), yielding **11.5013 CPU-hours** for the same unfinished fraction. Those are different operation units and no completed first-leaf calibration exists; this sensitivity cannot establish a gate pass. The conservative projection controls this stop. No four-leaf kernel stage was started.

Prepared [Batch38_0.lean](Batch38_0.lean) through the remaining layer batches and Assemble38.lean would move checkpoints across process/module boundaries; they were **not executed** after the cost gate. They have no measured speedup or acceptance claim.

## Enclosures, margins and operation counts

The compiled Int replay on node 38 agrees exactly with independent Python on **300 intermediate intervals / 600 endpoints**, and on final lower(-Y_0) = **-3580983288643415/1125899906842624** (measured endpoint, derived rational interpretation). Metered and unmetered results agree by #eval. Largest retained preactivation endpoint: **58 bits**, measured; Lean transient integer widths/allocations are **not found**. Evidence: [agreement-38.json](agreement-38.json), [int38-result.json](int38-result.json).

| Node | Step 1 exact-decimal margin, derived from measured Python endpoint | W2b margin, reported |
|---|---:|---:|
| 38 | 0.8105735675817493 | 0.8105735675817485 |
| 32 | 1.095726925481465 | 1.095726925481464 |
| 40 | 1.136066524012548 | 1.136066524012548 |
| 8 | 1.285645092350738 | 1.285645092350737 |

Only node 38 was replayed in Lean; the other rows are independent Python comparisons and prepared inputs, not additional Lean leaf successes. Exact fractions are in compared-margins.json. All differences are the same derived **5332804489/6871947673600000000000000**, below one grid unit: W2b rounds T as part of its running bias; this pilot derives -Y_0 separately and adds exact T only at comparison.

| Measured source-level operations, complete compiled node 38 replay | Monolithic | Checkpoint |
|---|---:|---:|
| add/subtract | 2118113 | 2118113 |
| multiply | 2301000 | 2301000 |
| Euclidean division, including directed rounding | 2413244 | 2413244 |
| signed comparison | 1560915 | 1622165 |

Checkpoint total **8454522** is a derived sum. Counters execute the same generic source under StateM Counts; kernel checks instantiate Id. Comparison increase **61250** is a measured difference from repeated local ReLU/adaptive setup. Unary negations, Nat control/index checks, counter bookkeeping and shape/final checks are excluded; allocations and GMP limb operations are not instrumented. Scope is explicit in int-counts-notes.md. This is neither an instruction count nor a simulated kernel timing.

SingleTargetCounts.lean measures **16930 add/subtract, 18434 multiply, 19322 divide, 12336 compare** for the deep local target: **67022** total (derived). Its standalone measured **12.78 CPU s** gives **0.190684 ms per counted operation** (derived, inclusive of import, declaration and axiom-audit overhead). It is a component rate, not a completed full-leaf throughput measurement. Dividing a censored full-leaf kernel run by the full compiled operation count would be invalid, so no such full-leaf rate is reported.

## Compilation, coverage and unmeasured costs

Measured successful Int data encoding uses explicit Int.ofNat / Int.negSucc constructors: **21.43 CPU s**, **21.53 s wall**, **2051424 KiB RSS**. Constructor reversal reproduces the original overloaded data source exactly (explicit-data-audit.json). The overloaded retry was stopped after **428.28 CPU s** without completion; the earlier default-heartbeat compile failed after **122.69 CPU s**. Those are elaboration failures/censored runs, not arithmetic failures. They remain in the resource ledger but are not projected as costs of the winning data encoding.

| Cost item | Evidence / status |
|---|---|
| Frozen Net compilation | measured 67.38 CPU s once; used by real semantics, independent of certificate |
| Int core + checkpoint core compilation | measured 2.87 + 1.94 CPU s |
| Explicit fixed Int data compilation | measured 21.43 CPU s once |
| Typed node input + proposal data | measured 2.06 + 2.39 CPU s for node 38; derived uniform 151.30 CPU s across 34, not an observed batch |
| Concrete coverage checker core + instance | measured 2.48 + 2.69 CPU s |
| Generic coverage/real soundness composition | unmeasured; not yet proved |
| Whole-leaf acceptance/axiom audit | unfinished; no final axiom closure for an accepted leaf |
| Export and nanoda for a real accepted leaf/full tree | not run: there is no completed accepted leaf to export |

Coverage.lean / CoverageData.lean kernel-check exact root containment, inherited boxes, strict interior shared closed cuts, valid indices and exactly-once traversal of the real tree. This is a Boolean coverage computation, not the missing generic coverage-to-safety theorem. Its axiom closure is standard. CoverageControls.lean rejects a reused child and changed cut; ChunkControls.lean rejects an intermediate endpoint shifted by one grid unit. These do not substitute for the later full unsafe-model mutation suite.

## Failures and limitations retained

- Initial signed-decomposition simplification omitted a sign hypothesis; corrected local proof and axiom audits pass.
- Forward setup initially omitted an importable generated .olean, then a Box namespace and tensor shape proof; corrected before arithmetic measurement. The first rational trace used an unavailable tensor accessor; corrected. These are setup/type errors, not verifier verdicts.
- Int core initially used reserved identifier prefix; corrected. The executable fixture initially compared Id-wrapped values without exposing Id.run; corrected. Chunk core initially used an Inhabited Layer lookup without a default; corrected.
- First overloaded integer data compile hit the default heartbeat limit; the retry removed it but remained too costly. Explicit constructors provide the measured faster import representation.
- Both whole-leaf monolithic kernel candidates OOM. The one-module checkpoint run is incomplete and deliberately stopped at the cost gate. No successful whole-leaf result is hidden among these runs.
- TorchLean's legal all-zero forward slopes are one choice; its failure does not prove all slope choices fail. Final forward margin is unavailable. Alternative algorithm/encoding improvements remain open, not benchmarked claims.
- Prepared per-process batches, checked linear witnesses and supplied-product packing were not run. Optional Step 1c is omitted after the mandatory first-leaf gates failed. No novelty claim, full safety claim or nanoda claim is made.

## Resource audit and operational deviations

Long kernel and evaluation jobs ran in dedicated systemd user units, MemoryMax=16G, two Lean threads and CPU affinity pairs, with logs. No large downloads, paid calls, GPU, network writes, pushes or upstream changes occurred. Initial/final free disk displays were **93G / 92G** (measured rounded df display), above the **45 GB reserve** (reported: brief). Recorded completed-run CPU totals are in resource-summary.json and runs.jsonl; short initial bootstrap compiles were not timed, so that sum is not a complete exact total. The elapsed-session/affinity upper bound is also recorded, far below the **48 CPU-hour cap** (reported: brief).

**Deviations:** initial short Rounding/Signed bootstrap commands used the inherited virtual-address limit rather than their own MemoryMax cgroups. Two short diagnostics (each under four seconds wall, measured) were launched while three Lean jobs were active, briefly allowing five Lean processes. This violated the requested process-count cap. It did not occur during the isolated final kernel cost pilot. The implicated final proof audits were repeated in capped units with compliant concurrency (rounding-final-audit, int-controls-final-audit, int-meter-final-audit). The launch mistake and original logs are retained; resource compliance is not overstated. RSS/cgroup differences are explained above rather than misreported as a raised cap.

## Artifacts and decision

SHA256SUMS binds final sources, generated inputs and completed logs; input-hashes.json provides the compact input/driver index. runs.jsonl appends experiment outcomes, including failed/stopped runs; duplicate time-file aliases are explicitly excluded from totals. README.md documents reproduction and trust boundaries.

**Decision:** stop these candidates. Do not label this certificate kernel-checked, and do not proceed directly to a large soundness proof for either tested driver. Keep the frozen semantic contract and signed local proofs; first demonstrate a complete real leaf under the time/memory gate with a cheaper computation proof boundary or checked witnesses. Full-tree timing, semantic soundness composition, final axiom audit and independent-kernel replay remain open.

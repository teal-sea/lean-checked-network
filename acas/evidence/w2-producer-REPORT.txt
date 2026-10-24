# W2 producer spike — final measured report

This spike has produced complete split/leaf evidence from the pinned alpha-beta-CROWN CLI on real ACAS Xu property-1 instances. It **did not establish exact acceptance of a complete original benchmark region** with the requested IBP-intermediate replay. All accepted-leaf tests must be read together with the separate coverage result.

## Installation and scope

Source versions (measured `git rev-parse`): alpha-beta-CROWN `b58d83ccb32469fc7ae9304fa1d33568ea76b00e`; its auto_LiRPA submodule `e3930353a3589f7d10879f1e71223d1eefb57196`; VNN-COMP benchmark repository `d9e7b2feeaf534dcc557729ee7c920bd5b97099c`. The repository category is `benchmarks/acasxu`, not `acasxu_2023`; its README reports that this is the same benchmark used in previous years. Source was downloaded through Git, not a repeated prior-art search.

Final supported environment: Python 3.11.17, PyTorch 2.11.0+cpu, torchvision 0.26.0, ONNX 1.23.2, NumPy 2.4.6 (measured installed versions). CPU only; OMP/MKL thread limits 8 (configured), explicit `torch.set_num_threads(8)` in the restricted driver. CLI runs are pinned to CPUs 0–7 (configured); longer checker jobs use user systemd units with MemoryMax=32G. No solver account/license or paid call was used. Gurobi's Python module is installed for upstream imports; none of these experiments invokes its solver.

A torchvision installation initially upgraded torch to 2.14.1+cpu; exploratory CLI results are retained under `cli-*` filenames. Torch/torchvision were then explicitly pinned to the supported versions above and producer runs repeated under `cli-supported-*`. Do not attribute the exploratory timings to the final environment. Exact Python checking imports no Torch, NumPy, ONNX or upstream verifier code.

## Instrumentation

`instrument.patch` contains all changes to the upstream clone: an opt-in `W2_CAPTURE` wrapper records bound computations with boxes, objectives, lower affine A/b, intermediate intervals and alpha values; input splitting records every binary split with parent/child endpoints; an additional hook records all domains immediately before terminal filtering. These are JSONL events, including nonterminal data, not merely a verdict log. Sparse-alpha indices are retained in raw events. The normalizer writes explicit node IDs and both children and checks coverage before labelling a certificate complete. No clipping, attacks, external cuts, or ReLU splitting are enabled. The raw event export retains intermediate alpha data which the restricted checker does not consume.

`producer.py` is a separate restricted driver against the pinned auto_LiRPA. It freezes IBP intermediate bounds, optimizes alpha, disables sparse alpha, and captures accepted leaves before dropping them. It is **not** a claim that the full CLI uses IBP intermediate bounds. Earlier sparse-alpha output was detected by independent replay and regenerated with dense alpha tensors; that aborted long producer attempt is not an acceptance result.

The benchmark parameters are read from float32 ONNX tensors and serialized as exactly representable Python floats; the checker interprets these as exact dyadic Fractions. The ONNX input subtraction constant was checked to be zero. Sequential MatMul/Add/ReLU structure is reconstructed; no broad ONNX-import correctness theorem is claimed.

VNNLIB endpoints are exact decimals. The outward runs replace them with enclosing binary32 endpoints, so no inward float cast silently drops a boundary. Coverage checks include enclosure of the original decimal box. Property 1 uses the original decimal threshold exactly in the normalized checker input, not the producer's rounded threshold. The model and property supplied to the checker must be trusted inputs; the manifest hash is an identity aid, not an independently verified importer or a cryptographic admission policy.

## Producer results currently available

All numbers in the following tables are measured unless explicitly labelled otherwise. Producer wall time includes interpreter/import/startup and instrumentation. CLI internal time excludes startup and is reported by the producer log. Experiments ran with other reference checkers sharing the CPU budget, so these timings are not isolated throughput benchmarks.

| Instance and method | CLI internal time (reported log), s | Wall time (measured), s | Leaves | Splits | Coverage |
|---|---:|---:|---:|---:|---|
| ACAS 1_1 / property 1, CROWN, supported | 4.7473 | 16.1912 | 34 | 33 | exact tree check passes |
| ACAS 1_5 / property 1, CROWN, supported | 5.9148 | 13.3414 | 30 | 29 | exact tree check passes |
| ACAS 1_1 / property 1, alpha-CROWN, supported | 21.1719 | 27.9196 | 22 | 21 | exact tree check passes |

The supported CROWN 1_1 certificate has exactly the same checker-relevant network, boxes, splits and slopes as the exploratory version (measured structural comparison); final affine float diagnostics and timing metadata are not part of that comparison.

| Supported-version evidence | JSON bytes | MessagePack bytes | zlib(MessagePack) bytes | Terminal leaves |
|---|---:|---:|---:|---:|
| CROWN 1_1 / property 1 | 327,958 | 127,944 | 60,570 | 34 |
| CROWN 1_5 / property 1 | 323,409 | 120,968 | 60,155 | 30 |
| alpha-CROWN 1_1 / property 1 | 331,574 | 107,004 | 64,236 | 22 |
| restricted IBP-alpha 1_5 / property 4, incomplete | 471,132 | 250,100 | 64,852 | 100 accepted leaves, 29 pending leaves (derived: 129 total leaves minus 100 accepted) |

MessagePack is numeric binary serialization with binary32 float encoding; exact-decimal/property strings are retained. Semantic fields survive binary round trip exactly (measured comparisons; producer-margin/timing diagnostics excluded). Sizes include the network, specification manifest and tree. Supported raw alpha-CROWN events occupy 20,763,938 bytes (measured), because intermediate optimization state is duplicated. The exploratory unsupported-version alpha run had 228 leaves and 144,696,663 raw event bytes (measured); those are not the supported run's results.

## Independent arithmetic checker

`exact_check.py` uses only Python standard-library Fraction/integer arithmetic. It recomputes IBP intermediate intervals from the network and each input box, then runs a backward CROWN pass using exported final-objective slopes. Slopes must lie in [0,1]. ReLU upper secants are recomputed from independently sound intervals. The exported floating A/b is diagnostic evidence; it is not accepted as a proof without derivation, and the checker does not demand bitwise equality to a newly recomputed bound.

The fixed-precision modes round every scalar arithmetic result outward at scales 2^-30, 2^-50 and 2^-80. Backward coefficients are intervals, so coefficient rounding is accounted for when forming the final affine expression. This checks a real-valued network with exact binary32 parameters, not deployed IEEE-754 evaluation.

Tree validation requires precisely two children, valid interior cuts, both children equal to the exact parent split, every reachable terminal having evidence, no duplicate/reused nodes, no unreachable nodes, and enclosure of the original decimal region. Closed children share the split hyperplane; there are no gaps and their interiors are disjoint. This is checked before arithmetic replay.

Arithmetic results so far (measured, **partial property-4 tree only**):

| Mode | Leaves checked | Pass | Fail / unproved | Minimum lower margin | Check seconds | Largest instrumented integer bits |
|---|---:|---:|---:|---:|---:|---:|
| Fraction | 100 | 100 | 0 | 0.000007133768851168117 | 103.1387 | 2,187 |
| 2^-30 | 100 | 92 | 8 | -0.00005538575351238251 | 92.7370 | 90 |
| 2^-50 | 100 | 100 | 0 | 0.000007133714102991462 | 100.1306 | 150 |
| 2^-80 | 100 | 100 | 0 | 0.000007133768851168081 | 97.8000 | 240 |

A negative lower margin means this replay cannot prove the leaf; it is not a counterexample or a demonstration that the producer's floating bound was unsound. The incomplete tree is rejected as an original-region certificate regardless of individual passes. Its regenerated producer run used the exploratory torch 2.14.1 environment; the independent arithmetic results concern the exported exact network/boxes/slopes and do not depend on Torch. All complete benchmark runs in the main table were repeated with supported torch 2.11.0. Full-region results below confirm that ordinary CROWN uses tighter intermediate bounds than the requested IBP replay needs; replacing those bounds loses acceptance even under exact arithmetic.

Counters record each explicit rational add/subtract/multiply/divide, directed rounding, and instrumented comparison, with numerator/denominator operand bit-length histograms in `runs.jsonl`. The integer-width maximum includes normalized arithmetic results and the integer scaling used in rounding. **Limitation:** these are rational-primitive counters, not a complete trace of internal Python Fraction GCD/cross-product integer operations; they must not be advertised as counting every low-level integer operation or the true maximum of hidden temporary integers. Further instrumentation is needed for that part of the requested Lean cost estimate.

## Controls and limitations

The complete exploratory CROWN certificate first passes exact tree coverage. Moving the lower boundary of terminal node 8 inward along input dimension 0 creates a gap; the checker rejects it with `box mismatch / gap` before bound replay (measured). Mutation is saved as `cert-cli-gap.json`. Separate small-network tests include a weight mutation that genuinely makes the property false, malformed alpha, outward arithmetic and incomplete-tree rejection: 13 tests pass (measured, tests.log). The real-benchmark negative control is the gap mutation, not the toy weight example.

No ReLU-split/beta instance was attempted: the input-split path already exposed the intermediate-bound replay blocker. No GPU execution was available. No Lean proof or kernel replay is produced by this worker. No novelty claim is made.

## Full-tree replay results

Every terminal leaf of each supported complete tree was replayed at every requested precision. All following numbers are measured. The CROWN 1_1 Fraction result uses the exploratory certificate after an exact structural equality check of every checker-relevant field against the supported certificate; its dyadic results were also run directly on the supported certificate. This equality excludes floating A/b and producer-margin diagnostics, which are not trusted by the replay.

| Complete certificate | Arithmetic | Pass / total | Weakest lower margin | Largest instrumented integer bits |
|---|---|---:|---:|---:|
| crown-1_1-p1 | Fraction | 0 / 34 | -752.989357751 | 18,199 |
| crown-1_1-p1 | 30 | 0 / 34 | -752.989900154 | 103 |
| crown-1_1-p1 | 50 | 0 / 34 | -752.989357751 | 163 |
| crown-1_1-p1 | 80 | 0 / 34 | -752.989357751 | 253 |
| crown-1_5-p1 | Fraction | 0 / 30 | -593.972752062 | 19,450 |
| crown-1_5-p1 | 30 | 0 / 30 | -593.973150404 | 102 |
| crown-1_5-p1 | 50 | 0 / 30 | -593.972752063 | 162 |
| crown-1_5-p1 | 80 | 0 / 30 | -593.972752062 | 252 |
| alpha-1_1-p1 | Fraction | 0 / 22 | -716.31964024 | 19,509 |
| alpha-1_1-p1 | 30 | 0 / 22 | -716.320230095 | 103 |
| alpha-1_1-p1 | 50 | 0 / 22 | -716.31964024 | 163 |
| alpha-1_1-p1 | 80 | 0 / 22 | -716.31964024 | 253 |

Every failed leaf's exact rational or dyadic margin is retained in `runs.jsonl` and/or the per-certificate `.check-*.json` file; no failed leaf is silently dropped. These are failure-to-prove margins, not concrete unsafe witnesses.

| Complete certificate | Rational +, -, ×, ÷ calls per replay | Fraction check time, s | Fraction sum of worker times, s | Fraction largest operand bits | Derived conservative hidden-temporary bit bound |
|---|---:|---:|---:|---:|---:|
| crown-1_1-p1 | 3,656,244 | 234.0196 | 234.0196 | 18,199 | 36,399 |
| crown-1_5-p1 | 3,235,044 | 56.1203 | 319.7733 | 19,450 | 38,901 |
| alpha-1_1-p1 | 2,367,260 | 36.8000 | 193.9149 | 19,509 | 39,019 |

The last column is **derived**, not a measured peak: multiplying two recorded numerator/denominator operands uses at most twice the largest operand width, and an addition can need one further bit. It bounds direct unreduced cross-products in the usual rational formulas; it is not a CPU-instruction trace or a statement about Lean implementation internals. Fraction 1_1 was sequential; the other Fraction rows used six standard-library worker processes within the shared eight-CPU affinity. Their wall times are not directly comparable to sequential timings. Per-precision operation types and operand histograms are in the JSONL log.

For the partial tree, each mode uses 10,457,504 explicit rational arithmetic calls (measured); the smallest exact leaf margin is approximately 7.13e-6 (measured). Exact fractions grow substantially more on the broad complete-tree leaves than on these narrow leaves. Fixed-scale arithmetic controls instrumented integer widths but does not repair loose intermediate enclosures.

## Negative controls

In addition to the exploratory gap test above, the **supported alpha-CROWN** certificate passes coverage, then moving terminal node 13's lower boundary inward along dimension 0 makes coverage fail with `box mismatch / gap` (measured). The mutation is saved as `cert-supported-alpha-gap.json`. This control isolates coverage validation even though the unmodified certificate's requested IBP replay already fails its leaf bounds.

## Answer and next step

**Can a GPU-found certificate be rechecked exactly, and how big is it?** No GPU run was measured. On the CPU producer, complete real ACAS input-split evidence was exported: 22–34 leaves and 107,004–127,944 bytes of numeric binary evidence, including the model and property (measured across the supported complete runs). Its covering tree checks exactly. But the requested IBP-intermediate/Fraction-CROWN replay accepts **zero** leaves on those complete certificates. A separate incomplete tree demonstrates successful exact replay of 100 real leaves, with loss at the coarser dyadic scale. This spike therefore does not justify an end-to-end exact-checking success claim for an original ACAS benchmark instance.

The important missing proof data is the derivation of the producer's tighter intermediate bounds. Raw capture retains their endpoints and intermediate alpha state, but endpoints alone are not trusted derivations. A next checker should verify intermediate CROWN lower/upper passes in topological order, or the producer must use weaker IBP-derived enclosures and potentially much more input splitting. This is an implementation/design inference from the measured replay failures, not a measured scaling prediction. Full low-level integer-operation instrumentation also remains unfinished; current rational-operation counts must be labelled accordingly.

## Reproduction and artifacts

From this work directory, with the installed `.venv` and fetched source:

```sh
OMP_NUM_THREADS=8 MKL_NUM_THREADS=8 .venv/bin/python run_cli.py cli-crown-outward.yaml NEW_TAG
OMP_NUM_THREADS=8 .venv/bin/python export_events.py NEW_TAG-events.jsonl NEW_CERT.json 1_1
.venv/bin/python exact_check.py NEW_CERT.json --precision exact
.venv/bin/python exact_check.py NEW_CERT.json --precision 50
.venv/bin/python -m pytest -q test_exact_check.py
```

Use the host's required user-systemd wrapper and MemoryMax for potentially long jobs; `check_parallel.py` provides the six-process arithmetic measurement path. `instrument.patch` applies at the alpha-beta-CROWN repository root. `producer.py` is the separately named IBP-restricted driver, not part of that patch. `runs.jsonl` is the completed-experiment ledger, including capped/incomplete runs and failures. `binary-sizes.log`, producer logs, certificate files, raw CLI events, tests and the independent checker are retained. No pushed commits, PRs or external messages were created.

Final resource check: work directory occupies 2,455,913,196 bytes and free filesystem space is 101,760,401,408 bytes (measured). All measurement services have exited (measured systemctl state); no long-running experiment is left active. The saved patch passes `git apply --reverse --check` against the modified checkout (measured).

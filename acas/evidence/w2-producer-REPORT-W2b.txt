# W2b — exact replay of real ACAS CROWN certificates

**Measured conclusion:** all three complete real ACAS certificates are accepted at every tested dyadic precision and by exact Fraction checking of independently verified intermediate proposals. The ordinary CROWN trees close with checker-chosen adaptive intermediate slopes; the alpha tree closes with captured target-specific intermediate alphas. The checker derives bounds topologically using backward CROWN and independently derived local IBP. No producer rerun, GPU execution, Lean soundness proof or Lean kernel replay is claimed.

All experiment numbers below are **measured**, except explicitly marked **derived**. Precision settings and source line numbers identify configurations and code rather than measured quantities. Existing certificates, producer logs and previous check results remain intact. New artifacts have the `crownint-` prefix; the authorized existing `exact_check.py` is extended in place. The first report draft was saved before the requested deadline.

## What the producer actually computes

Source snapshot: alpha-beta-CROWN `b58d83ccb32469fc7ae9304fa1d33568ea76b00e`, auto_LiRPA `e3930353a3589f7d10879f1e71223d1eefb57196` (measured again with local `git rev-parse`; reused without a new producer run). Exact checking uses Python 3.11.17 (measured).

Ordinary CROWN derives preactivation bounds by backward identity objectives, except the first affine layer and some operators handled directly by IBP (`abc/auto_LiRPA/auto_LiRPA/bound_general.py:1022–1111`). The adaptive lower ReLU slope is one iff u > -l, zero otherwise (`operators/relu.py:503–524,725–782`). Upper secants are based on the current preactivation interval.

**Sparse intermediate handling matters.** `bound_general.py:1143–1172` computes IBP reference bounds when needed. `backward_bound.py:449–525` selects the union of unstable target neurons across the batch; `backward_bound.py:649–692` restores IBP endpoints for unselected neurons. `interval_bound.py:154–188` derives IBP from existing sound earlier bounds, rather than necessarily propagating IBP from scratch through every earlier layer. Therefore not every captured endpoint is a dense backward CROWN result. The input-split caller (`abc/complete_verifier/input_split/batch_branch_and_bound.py:240–246`) supplies no reference intermediate bounds in these calls.

The alpha path sets `fix_interm_bounds=True` and calls `CROWN-Optimized` (`input_split/bounding.py:94–100,123–127`). That flag does **not** establish that all intermediates remain fixed: no explicit `interm_bounds` dictionary is supplied. `optimized_bounds.py:527–529,1152–1189` initializes via CROWN; `_set_alpha` (lines 117–135) adds all target-layer tensors to the optimizer; per-iteration `compute_bounds` (lines 729–743) can derive missing intermediate bounds. `operators/relu.py:725–782` chooses target- and side-specific alphas during opt/reuse. Raw terminal captures contain 61,447 distinct intermediate alpha values, including nonbinary values (measured, `crownint-alpha-state.json`). It would be incorrect to infer binary adaptive intermediates from the flag alone.

CROWN captures have empty alpha dictionaries. Alpha captures have dense tensors indexed by `(side, target neuron, domain, source ReLU neuron)` with target keys `/input-3`, `/input-7`, `/input-11`, `/input-15`, `/input-19`; `/44` is the final objective. Feature sparse indices are absent in these captures. `crownint-export-hints.py` extracts these arrays without rerunning Torch. Ordinary CROWN adaptive choices may also be reconstructed as untrusted slope hints from diagnostic intervals; those intervals are never accepted as premises.

## Independent checker and arithmetic

`exact_check.py` retains default IBP replay and adds `--intermediate crown` and `--intermediate crown-alpha`. For each preactivation, derive a lower bound with objective e_j and an upper bound by negating a lower bound for -e_j, using only previously proved intervals. Independently compute local IBP and intersect the two enclosures. Unlike the producer's sparse restoration, this checks every target and always permits a sound intersection. This is a sufficient independent proof, not a demand for bitwise reproduction of floating endpoints. All upper secants are recomputed; exported A/b and endpoints are not trusted.

Mode (a) selects adaptive lower slopes from the checker's own sound intervals. Mode (b), available if needed, uses captured per-target/per-side intermediate alphas, checking used slopes lie in [0,1]; the extraction validates every exported entry. For ordinary CROWN there are no exported intermediate tensors: reconstructed adaptive decisions are optional untrusted hints, not claims of exported optimized alphas.

Dyadic arithmetic rounds each scalar add/subtract/multiply/divide outward and maintains intervals for backward coefficients. `crownint-fast.py` implements this with explicit integer cross products on a fixed grid, avoiding Fraction GCD normalization. Random signed-rational differential tests compare every arithmetic operation and rounding direction against the Fraction implementation at each requested precision. Exact point-interval operations are shared in `ExactArithmetic` to avoid redundant identical work.

**Fraction row convention:** all scalar arithmetic is unrounded Fraction arithmetic, but intermediate intervals are dyadic proposals from the successful 2^-50 run. Each proposal is independently checked: exact backward CROWN and exact local IBP are derived first; only if the proposed interval encloses that derivation is it used in the next layer. Thus every intermediate endpoint has an exact derivation, and no exported endpoint is a premise. These rows are not wholly unrounded recursive endpoint selection. A separate wholly unrounded probe on terminal node 64 completed the first hidden layer in 0.00765 s (58 bits), the second in 0.4971 s (231 bits), the third in 2.3493 s (1,449 bits), and the fourth in 50.8191 s (18,835 bits), then hit a configured 300 s unit timeout while deriving the fifth layer (all measured). No completed wholly unrounded leaf is claimed; `crownint-unrounded-probe.log` and its termination record preserve this limitation. Accordingly the request for wholly unrounded Fraction replay of all leaves is not established. The complete Fraction measurements instead check every intermediate proposal with unrounded arithmetic. Commands can reproduce the Fraction mode using the generated option-(c) certificate.

## Replay table — all entries measured

Every row first passes exact covering-tree validation; no failed leaf is dropped. Positive margin means the objective exceeds the original exact threshold. Wall time includes the pool execution; worker-time sum is not CPU time. Runs use at most the allocated CPU budget, with competition and brief diagnostic-core sharing; these are not isolated throughput benchmarks.

| Certificate | Intermediate mode | Arithmetic | Pass / total | Weakest margin | Wall s | Sum worker s | Largest operand bits | Instrumented result/temporary bits |
|---|---|---|---:|---:|---:|---:|---:|---:|
| crown-1_1 | crown | Fraction, checked dyadic intermediates | 34 / 34 | 0.810573567666 | 118.0427 | 844.3816 | 4220 | 4220 |
| crown-1_1 | crown | 30 | 34 / 34 | 0.810462932102 | 128.1128 | 903.8799 | 50 | 110 |
| crown-1_1 | crown | 50 | 34 / 34 | 0.810573567582 | 161.8649 | 1169.8674 | 59 | 159 |
| crown-1_1 | crown | 80 | 34 / 34 | 0.810573567681 | 140.4334 | 991.7401 | 89 | 249 |
| crown-1_5 | crown | Fraction, checked dyadic intermediates | 30 / 30 | 1.31384204907 | 134.0389 | 973.3401 | 3817 | 3817 |
| crown-1_5 | crown | 30 | 30 / 30 | 1.31370680314 | 159.7029 | 1174.9100 | 50 | 110 |
| crown-1_5 | crown | 50 | 30 / 30 | 1.31384204899 | 156.2474 | 1166.5515 | 57 | 157 |
| crown-1_5 | crown | 80 | 30 / 30 | 1.31384204911 | 158.8819 | 1179.6646 | 87 | 247 |
| alpha-1_1 | crown-alpha | Fraction, checked dyadic intermediates | 22 / 22 | 0.44993410759 | 109.9313 | 711.8669 | 4671 | 4671 |
| alpha-1_1 | crown | 30 | 15 / 22 | -4.37055349536 | 88.7052 | 611.4431 | 50 | 110 |
| alpha-1_1 | crown-alpha | 30 | 22 / 22 | 0.449802530929 | 102.1233 | 705.7068 | 50 | 110 |
| alpha-1_1 | crown | 50 | 15 / 22 | -4.37031087134 | 90.9967 | 636.9795 | 60 | 160 |
| alpha-1_1 | crown-alpha | 50 | 22 / 22 | 0.449934107487 | 102.7743 | 697.3716 | 59 | 159 |
| alpha-1_1 | crown | 80 | 15 / 22 | -4.37031087112 | 93.3320 | 655.1143 | 90 | 250 |
| alpha-1_1 | crown-alpha | 80 | 22 / 22 | 0.449934107611 | 104.4313 | 730.0626 | 89 | 249 |

The fixed-grid temporary column includes explicit unreduced cross products and scaling integers. Fraction's column includes instrumented normalized operands/results; internal Fraction GCD/cross-products are not traced. A **derived** direct cross-product bound for Fraction arithmetic is twice the recorded maximum plus one bit. These notions must not be conflated.

## Diagnostic and negative controls

A preliminary dense CROWN replay that omitted local IBP intersection accepted only 28 / 34 CROWN 1_1 leaves at 2^-50, weakest margin -19.4690358845, wall 133.9115 s (measured). Preserved `crownint-dense-*` artifacts record the failure. Early tighter bounds can change subsequent adaptive slopes; “CROWN is tighter” does not ensure replay follows identical choices. Intersection of independently derived enclosures resolves that diagnostic case without trusting endpoints.

Gap controls mutate the first terminal's lower boundary inward for each complete certificate. All are rejected before bound replay with `box mismatch / gap` (measured; `crownint-gap-*.json`, `crownint-controls.json`).

The real weight control changes output-layer weight row 0, column 25 of ACAS 1_1 from -0.06271349638700485 to 1000000, leaving all other weights unchanged. The exact midpoint of terminal node 13 is a real counterexample: true property margin -178906.03322171202; checker margin -218297.11482987087 at 2^-50; replay elapsed 23.9030 s (measured). The exact witness coordinates and output fraction are in `crownint-controls.json`; the mutated network is `crownint-weight-mutation.json`. This is a genuine false-property mutation, not merely failure to prove a safe network.

Tests: 20 pass (measured, `crownint-tests-final-v3.log`), covering original tests, fixed-grid/Fraction differential arithmetic, sampled CROWN intermediate enclosures, independent side-specific hints, invalid slopes, ignored exported endpoints, and rejection of unjustified carried endpoints.

## Primitive counts for the winning dyadic mode

The winning mode is checker-adaptive CROWN for the ordinary trees and captured-intermediate-alpha CROWN for the alpha tree. All following values are measured at 2^-50. Counts are explicit rational/dyadic add, subtract, multiply and divide API operations; directed-round calls and API comparisons are separate. Python Fraction GCD/integer instructions, unary sign changes and structural/control comparisons are not included. Histogram observations count numerator and denominator operands, including exact model constants. These are checker primitive counts for a Lean design estimate, not measured Lean instruction counts.

| Certificate | Arithmetic primitives per leaf, min | Mean | Max | Total | Directed rounds per leaf, mean | API comparisons per leaf, mean | Max operand bits | Max explicit temporary bits |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| crown-1_1 | 3,207,890 | 3,921,432.1 | 4,556,710 | 133,328,692 | 3,921,432.1 | 1,167,955.0 | 59 | 159 |
| crown-1_5 | 4,556,618 | 5,116,829.5 | 5,721,462 | 153,504,884 | 5,116,829.5 | 1,477,685.1 | 57 | 157 |
| alpha-1_1 | 3,660,338 | 4,605,300.5 | 5,267,774 | 101,316,612 | 4,605,300.5 | 1,352,941.0 | 59 | 159 |

Per-leaf operation dictionaries and full operand-bit histograms are retained in `crownint-final-*-50-leaf-*.json` and each summary.

## Certificate contents and serialized sizes

Option (b), alphas only: model/property identity and exact parameters, original decimal specification plus enclosing root, covering split tree, objective index, final-objective ReLU alphas, and the agreed independent intermediate derivation rule. For the ordinary CROWN certificates closed by mode (a), no intermediate alpha tensors are necessary. For the alpha certificate when mode (b) is required, option (b) also carries the captured dense per-target/per-side intermediate alpha arrays, with no endpoint premises.

Option (c), intermediate bounds plus derivation hints: the same fields plus dyadic intermediate endpoint numerators and their scale, and rules specifying signed identity backward objectives, adaptive or captured lower slopes, recomputed upper secants and local IBP intersection. Layer/neuron positions identify the objectives implicitly. Each endpoint must pass its own derivation inequality before use. These files implement that check; endpoints alone are insufficient. Dense affine A/b is unnecessary for this variant.

The following are measured bytes, including model, manifest, property and tree. JSON uses decimal integers and exact strings; MessagePack encodes original binary32 values and endpoint integers. A semantic round trip is checked. zlib is applied to MessagePack. Compression is packaging, not part of the trusted arithmetic checker.

| Certificate | Option | JSON bytes | MessagePack bytes | zlib(MessagePack) bytes |
|---|---|---:|---:|---:|
| crown-1_1 | b | 322,193 | 126,056 | 59,337 |
| crown-1_1 | c | 699,822 | 321,447 | 224,748 |
| crown-1_5 | b | 318,329 | 119,300 | 59,075 |
| crown-1_5 | c | 643,585 | 291,735 | 201,803 |
| alpha-1_1 | b | 10,902,268 | 8,467,227 | 1,477,399 |
| alpha-1_1 | c | 11,146,904 | 8,593,751 | 1,598,932 |

## Reproduction

From this work directory, CPU-pinned under the required resource-capped user-systemd wrapper for long jobs:

```sh
.venv/bin/python exact_check.py cert-supported-crown-1_1-p1.json --precision 50 --intermediate crown --output crownint-NEW-check.json
.venv/bin/python exact_check.py crownint-option-c-crown-1_1.json --precision exact --intermediate crown --output crownint-NEW-fraction.json
.venv/bin/python -m pytest -q test_exact_check.py crownint-tests.py
```

`crownint-run.py` supplies the multi-process timing and detailed per-leaf artifacts; `crownint-resume.sh` controls the measurement campaign, using checked dyadic proposals for Fraction. `crownint-export-hints.py` extracts optional intermediate alphas. `crownint-controls.py` and `crownint-sizes.py` reproduce controls and packaging measurements. Finished experiments append to the original `runs.jsonl`; previous records are retained.

## Plain answer and limits

**Yes for real certificates produced by a GPU-capable verification tool running here on CPU:** complete ACAS regions are accepted by independent exact outward arithmetic after supplying or deriving sound intermediate CROWN bounds. For the complete ordinary-CROWN examples already closed, the certificate can contain only the covering tree and final alphas alongside the network/property; the checker derives intermediate bounds itself. Carrying proposed intermediate intervals with derivation hints additionally permits exact Fraction checking without unrestricted recursive denominator growth. Alpha-CROWN's optional target-specific intermediate slope state is retained for cases requiring it.

This is a working arithmetic prototype, not a Lean-proved checker or a GPU-run measurement. It verifies a real-valued network with exact binary32 parameters; deployed floating evaluation and importer correctness remain separate. No novelty or unmeasured scaling claim is made.

## Final audit (measured)

All 344 winning leaf replays across 12 complete-certificate/arithmetic combinations have positive exact rational margin signs. The audit recomputes tree membership, exact signs, minima and summed operation counts from saved leaf records, rather than trusting floating summary signs. All measurement units are inactive or in the expected timeout-failed state; no measurement job remains running. Free filesystem bytes at audit: 100279988224. Detailed record: `crownint-final-audit.json`.

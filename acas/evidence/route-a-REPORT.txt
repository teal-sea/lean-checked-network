# Route A: real batched dual pilot

**Arithmetic pilot gate: PASS.** Node 38's complete numerical receipt is accepted by the Lean kernel, with a positive exact margin. Measured data admission plus acceptance: **352.59 CPU s**; maximum measured process RSS: **4546972 KiB**. Derived uniform projection for the reported 34 leaves: **3.3300 CPU-hours**. Only the reported node 38 was emitted/accepted here; this projection is not a full-tree measurement.

The reported gate is at most 400 CPU s including data and acceptance, below 16 GiB, and a derived full-tree projection at most 4 CPU-hours. All Lean jobs were capped with `MemoryMax=16G`. This is a kernel-checked Boolean arithmetic receipt, **not yet a proved-sound checker for the real network**: executable list/offset correspondence, residual/telescoping soundness composition, importer correspondence, tree coverage and independent-kernel replay remain open. No novelty claim.

## Exact emitter and receipt

Measured emitter CPU: **1.188571290 s**; measured independent receipt replay CPU: **1.883984883 s**. `emit.py` uses exact integer arithmetic and audits every parameter against frozen `Net.lean`. `verify.py` independently checks the supplied products, all coefficient balances, residual endpoint/kink inequalities, bias/input sums, outward endpoint rounding, IBP intersections and the exact decimal strict threshold. It does not reconstruct slopes.

Measured dual column counts are `(501,401,301,201,101,1)`. Derived total dual/product entry counts are **75300 / 52755**. Measured maximum dual numerator width is **56 bits**. All required endpoint dependencies are retained. The producer chooses dyadic duals with integer rounding; the acceptance arithmetic is exact.

Measured exact margin numerator/denominator, with its rational interpretation derived:

`1211783778660853560685887064332051414124401203569759/2126764793255865396646091296448551321600000000000000`

Derived decimal margin: **0.5697779944935675**. The final comparison uses the reported exact threshold `3991125645861615/1000000000000000` and rejects equality. A measured extra smoke check evaluates all **501** telescoping identities at the box midpoint using exact rationals; this finite smoke is not a universal theorem. All algebraic coefficient balances are checked by the independent replay.

## Real packed block and controls

The checker traverses original integer lists inside the kernel, checks shapes and coefficient bounds, packs with Nat offsets, subtracts geometric offsets and checks packed equations. It never decodes digits or imports asserted packed literals. Reported design parameters are base `2^160`, weight/dual bounds `2^60`, and product bound `2^127`. The no-carry inequality is checked. Measured largest signed packed dual/product operands for the first block: **80049 / 80101 bits** (`sizes.json`).

Final noncomputable-data block measurements (all measured):

| Phase | CPU s | Wall s | Peak RSS KiB |
|---|---:|---:|---:|
| Data admission | 16.33 | 15.29 | 1887940 |
| Packed acceptance | 3.19 | 3.22 | 1915668 |
| Scalar exact-dot acceptance | 21.44 | 21.47 | 3608028 |
| Both corruption controls | 4.67 | 4.69 | 2014620 |

Derived scalar/packed acceptance ratio: **6.72×**, including imports. The scalar comparator checks the same exact product but omits packed-specific shape/bound work. Initial Mathlib-import measurements were **8.62 / 28.49 CPU s** packed/scalar; these are retained in `initial/` and `EXPERIMENT-NOTES.md`.

Both controls change one integer by one unit: a supplied product entry, then a weight. Both reduce to false in the kernel. The final noncomputable-data controls and scalar comparator are in `ControlsNC.lean` and `ScalarNC0.lean`; their timings are recorded separately and are not charged as per-node successful acceptance work. Final packed acceptances and controls have no axioms. `Injectivity.lean` ports `packed_inj`; `MatrixSound.lean` proves the generic bounded packed-matrix rule with standard axioms. The executable-list/offset bridge to that rule is still unproved.

## Complete node measurements

The final candidate uses noncomputable literal declarations, factored residual endpoint expressions, and Boolean comparisons of target-layer sum chunks. It recomputes exact residual minima rather than trusting imported minima. `same_spec` proves the Boolean comparison implies list equality. Each checked chunk is then reused for endpoint intersections and the strict final margin. All reported entries below are **measured**; CPU is GNU time user plus system and includes imports/elaboration/output.

| Phase | CPU s | Peak RSS KiB |
|---|---:|---:|
| datanc0 | 16.33 | 1887940 |
| datanc1 | 25.30 | 2027756 |
| datanc2 | 20.15 | 1953172 |
| datanc3 | 14.00 | 1835716 |
| datanc4 | 9.18 | 1743904 |
| datanc5 | 3.49 | 1642296 |
| nodedatanc-fixed | 2.91 | 1647140 |
| packednc0 | 3.19 | 1915668 |
| packednc1 | 4.78 | 2175780 |
| packednc2 | 4.86 | 2080060 |
| packednc3 | 3.66 | 1897548 |
| packednc4 | 3.15 | 1775396 |
| packednc5 | 2.19 | 1659828 |
| chunknc0 | 14.13 | 2035016 |
| chunknc1 | 16.85 | 2489804 |
| chunknc2 | 34.58 | 3135580 |
| chunknc3 | 41.79 | 3757496 |
| chunknc4 | 64.58 | 4546972 |
| chunknc5 | 16.01 | 3255772 |
| shapenc | 16.29 | 3218708 |
| endpointnc0-fixed | 1.89 | 1639132 |
| endpointnc1-fixed | 3.18 | 1771092 |
| endpointnc2-fixed | 3.18 | 1766484 |
| endpointnc3-fixed | 3.17 | 1770916 |
| endpointnc4-fixed | 3.16 | 1768832 |
| endpointnc5-fixed | 3.18 | 1779404 |
| marginnc-fixed | 15.76 | 3253944 |
| acceptnc-fixed | 1.65 | 1627144 |
| Data total (derived sum of measured phases) | 91.36 | — |
| Acceptance total (derived sum of measured phases) | 261.23 | — |
| Combined (derived sum) | 352.59 | — |

`AcceptNC.lean` assembles all reported six packed blocks, six interval-layer checks, the strict margin and the exact claim-vector length into `node38NC`. Its final axiom audit is in `acceptnc-fixed.log`. Static generic proof/core compilation, untrusted emission, diagnostic controls and failed engineering candidates are separately logged; they are not silently included in the per-node total. Measured one-time core/generic-proof compilation is **22.71 CPU s** (`pack-lean`, `block-lean`, `nodenc`, `samespec-v2`, `inj`, `matrixsound`). Adding that once to the measured node cost gives **375.30 CPU s** (derived sum), also below the reported gate. Untrusted emission and independent Python replay add their separately reported costs.

The projection conservatively repeats all measured node-specific data work for every reported leaf, including weights that a later implementation could share. It excludes unimplemented semantic soundness/coverage work and independent replay.

## Failed and superseded runs

The unfactored direct-list-equality balance driver was stopped at **327.35 CPU s** without acceptance. With completed data/products, its unfinished total was **505.64 CPU s**, an unfinished engineering run already beyond the cost gate. The factored executable-data direct-equality candidate was stopped at **298.77 CPU s**; the noncomputable direct-equality candidate at **155.91 CPU s**. The subsequent noncomputable Boolean monolithic attempt was stopped at **423.31 CPU s**, still without acceptance, when the bias-vector bug was found. These are censored runs, not arithmetic rejections, OOMs, or successful timings. GNU time prints a misleading zero exit field on signal termination; the ledger records signal status **143**. No speedup is inferred from those incomplete runs.

The initial Lean emitter also incorrectly retained all five final output biases instead of only output zero, creating four trailing claim entries. That bug was found during source inspection and fixed before the final chunked acceptance; an additional kernel theorem checks the corrected claim-vector length. The stopped monolithic candidates therefore have both a cost limitation and this structural bug; they are not clean performance measurements of the corrected checker. No isolated speedup is claimed for factoring, Boolean comparison or chunking. The final combined comparison/chunking/fixed-bias driver is the only completed full-node result. The Boolean-comparison lemma initially failed to elaborate; its corrected proof audits with `[propext]` and no admissions. Initial setup failures included systemd working-directory/environment forwarding, one missing section terminator and one missing parenthesis. The first endpoint bootstrap tried to import a deliberately stopped balance proof and failed; it is retained as `endpointnc0-bootstrap.*`. These are setup failures, not accepted arithmetic evidence. Raw final logs and the append-only ledger retain the outcomes.

## Hashes, resources and plain answer

Measured SHA256:

| Input | SHA256 |
|---|---|
| Frozen `Net.lean` | `4f89de9f7ca25762b638c97a51625d0c1065a0d3b5ab2ffe5de3ba7f32964426` |
| Producer certificate | `89d8742b8a08f2259dfb99f8dcac061cad9276db1fb75fb2d5a896ed89cc0b0f` |
| Emitted exact receipt | `f5d43acd50bd6fa711e06df32297d4799fc9862e878033c5435b1238c2a6cf49` |

`SHA256SUMS` binds the sources and generated artifacts; `runs.jsonl` logs completed experiments. `reproduce.sh` rebuilds the final candidate from the pinned existing cache. Measured deterministic regeneration preserved all **34** final source files byte-for-byte (`regeneration-audit.json`). Python probes used the host standard-library interpreter directly; no Python packages were installed. Work stayed in this directory; no upstream edits, downloads, network writes or subagents were used. Reported resource allocation was at most six cores and two Lean processes; actual Lean jobs used pinned pairs within that allocation. Measured initial free disk was the rounded `91G` display; measured later free disk was **96668106752 bytes**, above the reported **45 GB** reserve (`disk-final.txt`). Measured report birth time was **2026-10-23 19:56:11 UTC**, before the reported twenty-minute deadline.

**Plain answer:** the real packed product check works and rejects the requested corruptions. The full numerical receipt is kernel-accepted with a positive exact margin. The stated arithmetic performance gate **passes** on this host. Proceed to the missing soundness/import/coverage proofs only with the measured arithmetic scope kept explicit.

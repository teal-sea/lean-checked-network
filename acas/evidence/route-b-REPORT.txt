# Route B: dual receipts with justified intermediate cuts

**Gate 1 fails for the certificates found here; Phase 2 was not run.** All leaves close under exact arithmetic after adding justified cuts, but their checked work exceeds the operation budget. IBP alone cannot support one receipt per leaf: exact feasible relaxation countermodels establish insufficiency. No Lean acceptance or soundness theorem is claimed.

Plain answer: **one receipt per piece with only IBP is insufficient.** Receipts with extra endpoint witnesses establish positive bounds in the Python arithmetic experiment, but fail the requested cost gate. **Whole-proof Lean time is not measured**, because the brief requires stopping before the Lean pilot when Gate 1 fails. The intended statement is the frozen real-valued network property, not aircraft behavior or IEEE execution.

All table margins, witness counts, and source-level operation counts are **measured**; displayed decimal margins are **derived rounded views** of the exact fractions saved in JSON. Nodes and schema names are identifiers. The threshold, grid scales and arithmetic formulas are **derived exact constants**. Gate limits are **reported (brief)**. No novelty claim.

## Method and exact boundary

`probe.py` independently parses all rational parameter literals in frozen Net.lean and checks equality with the producer parameters. Every weight/bias is exactly representable on Q=2^50. The checked objective is f=-Y_0, with beta=-b_out and c=-W_out[0]; acceptance is the strict comparison T+lower(f)>0 for exact T=3991125645861615/1000000000000000. Initial leaf boxes and complete split-tree coverage are validated by the copied Step 1 tree checker.

IBP computes exact integer dot products, divides only once at the end of each row, and rounds each endpoint outward. The untrusted HiGHS LP has exact affine equations, stable ReLU equalities, and the standard triangle constraints on unstable ReLUs. Equality duals are rounded to dyadic numerators. The checker accepts arbitrary such duals: it recomputes W^T nu, bias contributions, input-box minima and every local endpoint/kink residual minimum. All receipt sums use denominator Q^3; no floating value participates in acceptance.

`sparse.py` ranks candidate endpoint tightenings by improvement of the fixed final dual bound after downstream IBP propagation. Candidate discovery uses adaptive CROWN, but each selected endpoint gets its own LP-optimized dual witness over strictly earlier layers. Its exact lower bound is rounded down; the negated lower bound gives an outward upper endpoint. Cuts are applied in order and downstream IBP intervals are recomputed and intersected with already justified cuts. No producer intermediate endpoint is assumed.

`audit.py` greedily deletes witnesses and recomputes all remaining endpoint values from their duals, repeatedly until no single remaining deletion preserves acceptance. This establishes inclusion minimality **for this fixed family of duals and this deletion procedure**, not a globally smallest certificate or a lower bound on every possible route-B proof. The LP is reoptimized during discovery, not during deletion. The final dual is fixed during pruning. Pruning caches linear contractions only to speed the search; final checker counts include those contractions.

## Per-leaf results

The first margin column uses IBP alone; the second uses the minimized cut receipt. All deletion pruning is complete. Each linked JSON stores the exact fraction margin, dual vectors, endpoints and acyclic witness order; displayed decimals are derived rounded views. The q values are inclusion minimal for the selected fixed duals, not globally minimum.

| Node | IBP-only margin | Cut margin | q | Receipt arithmetic ops | Total incl. repeated IBP | Pruned |
|---|---:|---:|---:|---:|---:|---|
| [13](min-13.json) | -697.183774 | 0.00242297212 | 108 | 979654 | 5645804 | * |
| [39](min-39.json) | -304.847591 | 0.0261902062 | 67 | 462074 | 3806474 | * |
| [40](min-40.json) | -451.508519 | 0.0166236642 | 154 | 1776601 | 7344651 | * |
| [31](min-31.json) | -327.691346 | 0.0488452489 | 69 | 464974 | 3933774 | * |
| [32](min-32.json) | -439.447756 | 0.0108688077 | 137 | 1474158 | 6731208 | * |
| [53](min-53.json) | -183.608433 | 0.0751194069 | 80 | 724566 | 4224466 | * |
| [54](min-54.json) | -156.673252 | 0.106332271 | [65](min-65.json) | 505441 | 3601041 | * |
| [49](min-49.json) | -159.831935 | 0.0104651563 | 67 | 578455 | 3611855 | * |
| [50](min-50.json) | -152.644142 | 0.0712985665 | [64](min-64.json) | 451613 | 3624963 | * |
| [24](min-24.json) | -378.180775 | 0.00262025237 | 117 | 1148507 | 5954607 | * |
| [37](min-37.json) | -254.00245 | 0.00016773208 | 96 | 811405 | 5135455 | * |
| [38](min-38.json) | -336.225065 | 0.00119693277 | 179 | 2385669 | 7984819 | * |
| [27](min-27.json) | -293.742164 | 0.02961669 | 97 | 800527 | 5217877 | * |
| [59](min-59.json) | -157.435153 | 0.0455249856 | [63](min-63.json) | 415421 | 3619871 | * |
| 65 | -168.639651 | 0.00564773986 | 85 | 795614 | 4435464 | * |
| [66](min-66.json) | -166.873634 | 0.0415566196 | 83 | 775401 | 4337501 | * |
| 63 | -179.047401 | 0.00802398451 | 105 | 1096871 | 5249871 | * |
| 64 | -176.977486 | 0.000132124274 | 106 | 1109928 | 5294028 | * |
| [57](min-57.json) | -184.426454 | 0.0394340403 | 75 | 548587 | 4188437 | * |
| [58](min-58.json) | -272.157911 | 0.00497362338 | 143 | 1703621 | 6742971 | * |
| [55](min-55.json) | -470.823589 | 0.000283063794 | 200 | 2684344 | 8858844 | * |
| [56](min-56.json) | -416.614752 | 0.0115334428 | 152 | 1744209 | 7265609 | * |
| [46](min-46.json) | -541.554364 | 0.00169394744 | 114 | 1056337 | 5909087 | * |
| [51](min-51.json) | -378.320037 | 0.0101949164 | 140 | 1576489 | 6755789 | * |
| [52](min-52.json) | -356.995327 | 0.00840251931 | 149 | 1700418 | 7144068 | * |
| [36](min-36.json) | -479.633258 | 0.00977069302 | 105 | 974932 | 5454482 | * |
| [17](min-17.json) | -703.877314 | 0.00354099141 | 105 | 979524 | 5443524 | * |
| [29](min-29.json) | -473.241269 | 0.00258255981 | 96 | 822639 | 5115589 | * |
| [30](min-30.json) | -462.168679 | 0.00783361946 | 91 | 763014 | 4884914 | * |
| [41](min-41.json) | -387.705678 | 0.000450098778 | 177 | 2225792 | 8120392 | * |
| [42](min-42.json) | -337.100467 | 0.0271183123 | 87 | 734972 | 4670272 | * |
| [33](min-33.json) | -372.393587 | 0.00682458778 | 135 | 1465581 | 6613781 | * |
| [34](min-34.json) | -288.663841 | 0.0764178508 | 69 | 499558 | 3875058 | * |
| [8](min-8.json) | -654.767284 | 0.00840264591 | 152 | 1774945 | 7218595 | * |

Operation scope: integer multiply, add/subtract, signed compare, and directed division; unary negation, list/index/control work, solver work and pruning trials are excluded. All table counts come from final uncached strict replay. Earlier discovery counts in the run ledger used a preliminary counter profile; they are superseded for the gate by final-results.json. Integer additions begin from zero in each dot product; bias scaling, endpoint floor division, target-row sign scaling, and endpoint acceptance comparisons are charged. Shape/index/control work and final strict comparison are excluded, matching the stated baseline scope. IBP charges the actual repeated row work, sign tests, intersection/order comparisons and ReLU endpoint tests. Repeated downstream IBP is charged rather than treating its tightened domains as free. Counts are not GMP limb operations or kernel timings. Baseline is reported 8,454,522 operations per leaf; Gate 1 permits a derived average of 845,452.2. The dual contractions alone are also reported so the effect of repeated IBP is visible.

## Final measured arithmetic result

- Accepted leaves: **34** (measured).
- Retained extra endpoint receipts: **3732** total, **109.764706** average (measured count; derived mean); range **63–200** (derived extrema).
- Smallest checked margin: **0.000132124273579** (derived decimal view of a measured exact margin).
- Receipt arithmetic: **38,011,841** operations total (measured counter sum).
- Including repeated IBP: **188,015,141** operations total (measured counter sum).
- Reduction versus the reported old replay: **1.528886x** (derived using uniform baseline per leaf); required reduction is **10x** (reported brief).
- Final uncached all-leaf strict audit: **14.509525 s wall** (measured Python elapsed time; not Lean time).

The smallest possible q over all choices of duals, endpoint locations and cut-search strategies was **not found**. The tested deletion search cannot establish that the entire sparse route is impossible. The precise negative result is: q=0 on the initial IBP relaxation is impossible here, and this LP-cut certificate family fails the cost gate even after deletion pruning. To continue, the specific missing ingredient is a substantially smaller cut basis (with reoptimized duals/support search), or deterministic batching/packing of the shared matrix contractions and shared bound refinements, followed by a new counted-cost test. The existing result does not justify starting a whole-checker Lean proof or assuming either improvement will meet the kernel budget.

## Controls and relaxation insufficiency

All requested controls have completed: a large corrupted final-dual entry destroys strict positivity; the real unsafe-weight mutation is rejected on node 13, which contains its exact rational counterexample; an overstated intermediate endpoint by one grid unit is rejected. Exact margins, changed weight, counterexample and output are in `controls.json`. A one-unit change to an arbitrary dual need not reject: arbitrary duals are sound, and a sufficiently small change can retain a positive bound. The corruption control deliberately changes it enough to invalidate acceptance.

`primal.py` constructs exact rational feasible points of each initial IBP triangle LP from the untrusted primal proposal. It recomputes affine preactivations exactly, fixes stable units, and clips unstable outputs into their exact valid triangle interval. All resulting relaxed outputs violate the property. This establishes that no dual for this **same IBP relaxation** can prove these leaves. These are relaxation countermodels, not counterexamples to the original ReLU network. Full exact points and their negative margins are in `primal-N.json` / `primal-results.json`.

## Lean and gates

No Lean process was launched. **Gate 1 fails**: all 34 leaves accept (measured), but average total work is **5,529,857.1 operations per leaf** (derived mean of measured counters), against **845,452.2** allowed (derived from reported baseline). Even excluding all IBP work, receipt arithmetic averages **1,117,995.3** (derived), above the limit. Gate 2 and full-tree Lean time are **not measured**. No timing projection substitutes for a kernel run.

The prospective checker computes: network/shape validation; outward IBP; an ordered list of truncated-network endpoint receipts; outward endpoint intersection and downstream IBP; the final residual lower bound; strict exact decimal comparison. Step 2 must prove the telescoping identity, endpoint/kink minimum lemma, IBP soundness, ordered-cut invariant, coverage composition, and bridge to frozen real semantics. No such whole-checker theorem is supplied here.

## Inputs and resources

Measured SHA256 fingerprints:

- `../step0/Net.lean`: `4f89de9f7ca25762b638c97a51625d0c1065a0d3b5ab2ffe5de3ba7f32964426`
- `../step0/Spec.lean`: `fc9a750a19646c2e66ced81bb8138620861b4c01e1fd0cd9b85baf1030e1a9b0`
- `../w2-producer/work/cert-supported-crown-1_1-p1.json`: `89d8742b8a08f2259dfb99f8dcac061cad9276db1fb75fb2d5a896ed89cc0b0f`
- `../w2-producer/work/crownint-weight-mutation.json`: `67c1f811878b58422c76c886bac96c5a12ebfbe18aefdb854570559d8fb8d297`

All writes are inside route-b. Solver threads are pinned to one; the campaign uses a systemd user unit with MemoryMax=16G. Pruning is in another capped unit. No Lean concurrency is used. Measured free disk at start and during the run is 91G (rounded df display), above the reported 45 GB floor. The local scipy/numpy venv occupies part of the measured workspace footprint; no paid calls or network writes were made. Prior-art sections were read, not repeated. `runs.jsonl` records completed experiments, including the unsuccessful early sparse-CROWN strategies; these must not be confused with the LP-endpoint candidate used for the final table.

## Final controls and provenance notes

- `corrupted-final-nu`: rejected (measured); checked margin -394864614.399 (derived decimal view; exact fraction in controls.json).
- `real-unsafe-weight-mutation`: rejected (measured); checked margin -3868601.30893 (derived decimal view; exact fraction in controls.json).
- `overstated-intermediate-endpoint`: rejected (measured).

The mutation changes exactly the producer-specified output weight (measured); its input is inside node 13 and its exact real output exceeds T. Original hidden-layer endpoint receipts remain valid because this mutation affects only the output layer. The checker recomputes the changed objective coefficients and rejects. Python arithmetic checking is not an independent Lean implementation: discovery, pruning and final strict replay share the residual-checking routine. The exact feasible-primal audit uses a separate Fraction construction and cross-checks the IBP-only relaxation result.

Measured resource ledger (GNU time; the multiprocessing parent totals omit worker CPU, as corrected below):

| Job | User CPU s | System CPU s | Wall | Peak RSS KiB |
|---|---:|---:|---|---:|
| all-leaf producer | 430.05 | 2.42 | 7:14.90 | 102212 |
| all-leaf pruning, excluding separately pruned nodes | 0.67 | 0.09 | 8:22.69 | 81896 |
| node 32 separate pruning | 106.95 | 0.55 | 1:52.75 | 80836 |
| final uncached replay | 15.12 | 0.09 | 0:15.23 | 80824 |

For all-leaf pruning, GNU time captured only the parent CPU; **0.76 CPU s is not the worker total**. The systemd unit journal measures **2230.763 CPU s** for that unit and a rounded **147.4M** cgroup memory peak (measured journal display). The producer unit measures **432.485 CPU s**, separate node 32 pruning **107.520 CPU s**, and the two final uncached audits **14.719 / 15.228 CPU s** (measured systemd journal). Full unit evidence is in resources-units.log. RSS in the GNU time table is a process measure and is not the summed worker memory or cgroup peak.

Node 38 separate pruning measured wall time is in min-38.json; its CPU and peak RSS were not separately captured. Short bootstrap/control/IBP-primal jobs are logged but not all were CPU-timed, so the resource table is not a complete session CPU total. No Lean timing, allocation or kernel-throughput measurement exists for route B. Long jobs ran under capped systemd units; solver and BLAS threads were pinned to one and total worker concurrency stayed within the reported eight-core allowance. No subagents were used. The first report draft preceded experiments and was refined in place within the reported twenty-minute draft requirement.

# ACAS certificate: status

Release packaging started 2026-10-24. The pull request remains a draft. The release gates
below apply to the packaged bytes; historical measurements are identified separately.
No larger-model or deployment result is claimed.

## Release gates

| Gate | Current result | Evidence |
| --- | --- | --- |
| Frozen statement and network binding | passed (measured, 2026-10-24); original specification hash restored exactly | `gen/audit.py`, `gen/source-provenance.json` |
| Pinned dependencies from GitHub, Mathlib cache | passed (measured, 2026-10-24) | release dependency log; committed `lean/lake-manifest.json` |
| Fresh source build, including TorchLean | passed: 1,091 new modules and 793 pinned dependency modules compiled (measured, 2026-10-24) | resource-bounded `gen/build.py --all --replay` |
| Exact final axiom list | exactly propext, Classical.choice, Quot.sound (measured, 2026-10-24) | final build log, then `gen/audit.py` |
| Source scan for admissions and unsafe evaluation | passed on all 1,091 new modules (measured, 2026-10-24) | `gen/audit.py` |
| Clean-environment Lean kernel replay of every new module | all 1,091 passed (measured, 2026-10-24) | per-module state and logs |
| nanoda on final theorem closure, hard standard-axiom allowlist | passed; Checked 59489 declarations with no typechecker errors, 1 pretty printer errors: [ (measured, 2026-10-24) | `gen/nanoda.py` |
| Changed weight, corrupted dual, coverage gap, real unsafe weight | all four reject by proved Boolean false; compilation and replay pass (measured, 2026-10-24) | `ControlWeight`, `ControlDual`, `CoverageControl`, `UnsafeControl13` |
| Byte-for-byte regeneration of every generated Lean file | passed: 1,055 generated files match (measured, 2026-10-24) | `gen/regenerate.py --check` |
| Python tests | 26 passed (measured, 2026-10-24) | captured pytest output |
| Independent exact Python receipt replay | all 34 passed; three stale/corrupt receipt controls rejected (measured, 2026-10-24) | `gen/independent.py` |
| Existing repository CI | passed on initial published head 702695a (measured, 2026-10-24); final-head results are linked from the draft PR checks and recorded in the external release report | existing workflows unchanged; captured check-runs response |

The ACAS proof is not added to CI. The release new-module compilation plus replay cost
**11.7639 CPU-hours (derived sum of captured successful-run times)** on the project host,
excluding dependency bootstrap, export and the independent checker. The existing `check.yml`
Lean job has a **240-minute timeout (reported workflow setting)** and also checks other
networks. A fresh hosted-runner ACAS build has not been shown to fit its limit. The
standalone commands retain the complete gate instead of weakening CI's existing checks.

## Release build measurements

The following counts and RSS maxima are measured from captured successful GNU time runs;
CPU and elapsed sums are derived. They apply to the final Lean source bytes.

| Phase | Successful runs (measured) | CPU seconds (derived) | Sum of elapsed seconds (derived) | Peak RSS KiB (measured) |
| --- | ---: | ---: | ---: | ---: |
| New ACAS compilation | 1,091 | 16,117.26 | 16,183.81 | 9,594,708 |
| New ACAS kernel replay | 1,091 | 26,232.83 | 26,703.03 | 8,985,360 |
| Pinned dependency source compilation | 793 | 2,828.92 | 2,594.33 | 2,174,248 |

The source-build/replay launch span was **14,407.26 seconds (derived from captured start
and finish timestamps)**. It includes the additional dependency checks and coordination
gaps; it is not a sum of serial module times. The new-module CPU totals exclude dependency
bootstrap, export and nanoda. See `evidence/release/timing-summary.json` and its raw logs.

The initial runner also replayed unchanged dependencies. **569 such replays completed
(measured)**. One additional FloatLib subtraction replay was deliberately stopped after
**2,338.61 seconds elapsed (measured wrapper)** and **2,324.65 CPU seconds (derived GNU
time sum)**, with **12,240,264 KiB peak RSS (measured)**. Its source compilation had passed
in **8.25 CPU seconds (derived)**. This interrupted extra check is retained in the run ledger;
it is not a kernel rejection or an ACAS negative-control result. The documented default now
replays every new ACAS module. Optional `--replay-dependencies` adds unchanged dependencies.
Nanoda checks the complete used declaration closure under the hard axiom allowlist, as recorded below.

Leanexport completed in **107.10 seconds wall (measured)** and **106.84 CPU seconds
(derived)**, with **8,938,116 KiB peak RSS (measured)**. Nanoda completed in **8351.22 seconds wall (measured)** and **8331.88 CPU seconds (derived)**, with **3,815,352 KiB peak RSS (measured)**. Its exact success line is:

```text
Checked 59489 declarations with no typechecker errors, 1 pretty printer errors: [
```

The object manifest was unchanged across export and independent replay (measured SHA256 comparison).

## Recorded project gates

The following rows summarize captured pre-packaging experiments, not fresh release
measurements. Values labelled measured come from the archived time/counter records or
tool logs. Sums and projections are labelled derived. Dates come from run timestamps.
The historical report snapshots in `evidence/*.txt` preserve interpretation and failures.

| Date | Gate / experiment | Result and recorded cost | Evidence |
| --- | --- | --- | --- |
| 2026-10-23 | Frozen input/specification review | passed; independent import audit matched all 13,305 parameters and 100 rational outputs (measured) | step0 review, `step0-validation.json`, importer manifest |
| 2026-10-23 | CPU CROWN producer, network 1_1 property 1 | 34 leaves, 33 splits; 16.1912 seconds wall (measured), 4.7473 seconds internal (reported producer log) | `w2-producer-work-cli-supported-crown-timing.log`, producer snapshot |
| 2026-10-23 | Independent backward checker | all 34 leaves accepted at each tested grid and with checked Fraction endpoint proposals (measured); fully unrounded recursion did not finish | W2b snapshot and captured checker records |
| 2026-10-23 | TorchLean forward rational kernel pilot, node 38 | OOM under configured 16 GiB cap; 275.96707 seconds wall and 133.612233 CPU seconds (measured); final margin unavailable | step1 snapshot and run ledger |
| 2026-10-23 | Monolithic integer backward kernel pilot, node 38 | OOM; 591.16 seconds wall, 582.98 CPU seconds, 18,186,736 KiB peak process RSS (measured) | `history/int38-kernel.time`, unit log |
| 2026-10-23 | Checkpoint integer backward, separate declarations in one module | stopped unfinished at 1,422.52 CPU seconds (measured); uniform projection 13.4349 CPU-hours (derived), exceeding the reported gate | step1 ledger and snapshot |
| 2026-10-23 | Route B: sparse duals plus justified cuts | 34 leaves close (measured), but 188,015,141 total counted operations (measured); average 5,529,857.1 (derived), above allowed 845,452.2 (derived from reported gate). No Lean pilot | `route-b-summary.json`, final-results and validation |
| 2026-10-23 | Route A complete weak-leaf receipt | passed; data plus acceptance 352.59 CPU seconds (derived sum of measured times), peak 4,546,972 KiB (measured); projection 3.3300 CPU-hours (derived) | `route-a-timing-summary.json` |
| 2026-10-23 | Route A whole-tree arithmetic | all 34 leaves accepted (measured); 38.10 minutes elapsed (measured), 3.4594 CPU-hours (derived); no semantic soundness claim at that stage | `route-a-all-timing-summary.json`, run ledger |
| 2026-10-23 | Arithmetic replay | 966 modules passed (measured); 10,133.26 CPU seconds (derived sum) | same |
| 2026-10-24 | Complete frozen theorem and semantic composition | proved; exactly propext, Classical.choice, Quot.sound (measured axiom output); 121 new proof modules replayed (measured) | step2 snapshot, timing-summary and ledger |

Historical runs used different process allocations. The whole-tree arithmetic experiment
used up to six jobs. The semantic stage recorded a brief five-job overlap before slot
locks were added. Those are disclosed in the snapshots; the release runner enforces the
four-job limit. Historical process RSS can exceed cgroup-charged memory because imported
mappings are shared; an OOM is identified from the unit result, not guessed from RSS.

The weak leaf's exact receipt margin is
`1211783778660853560685887064332051414124401203569759 /
2126764793255865396646091296448551321600000000000000`
(measured receipt, with its rational interpretation derived).
The decimal view **0.5697779944935675** is derived. Other valid checking algorithms may
produce different positive margins; bitwise agreement with a floating producer is not required.

## Files and trust boundary

`lean/ACASChecked/Final.lean` is the theorem root. The module paths use `ACASChecked.*`;
the reviewed `Frozen`, `CertSound`, receipt and algebra namespaces are preserved.
The proposition text is unchanged. Replacing its single prefixed import recovers the
original specification SHA256
`fc9a750a19646c2e66ced81bb8138620861b4c01e1fd0cd9b85baf1030e1a9b0` (checked by a test).
The network source is byte-identical to the frozen source. Only the theorem's exported
name is placed under `ACASChecked`.

All new arithmetic is kernel reduction or ordinary proofs. A compiled Python/producer
verdict is never promoted into a Lean theorem. The final nanoda gate exports only the
named theorem and its declaration closure, permits exactly the standard axioms with hard
errors, and records SHA256 of all .olean objects and their companions on the export search path. Its successful declaration count is quoted above and preserved in the raw log.

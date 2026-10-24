# Frozen ACAS theorem: completed

`Final.lean` compiles `theorem acas_1_1_property1 : Frozen.ACASXu_1_1_Property1`
with no hypotheses. Measured axiom output:

```text
'acas_1_1_property1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Measured: all 121 new proof modules passed clean-environment `leanchecker` replay.
`verification-manifest.json` binds each source, olean and replay outcome. No sorry,
`native_decide`, admissions or custom axiom declarations occur in the new sources
(measured source audit). The original and copied `Spec.lean` retain the required hash
`fc9a750a19646c2e66ced81bb8138620861b4c01e1fd0cd9b85baf1030e1a9b0`
(measured). Frozen Net hash also matches the supplied hash (measured input-audit.json).

## What closes the proof

- `PackingBridge.lean` / `RouteA.block_sound_list` connects the executable Nat-offset/list check to
  integer entrywise matrix equality using the imported packed injectivity theorem.
- `LocalReceipt`, `ListAlgebra`, `BackwardLists`, `RawColumns`, `SelectedWitness`
  and `FinalWitness` connect residual minima, all supplied products, column indexing,
  bias sums and input costs to the telescoping identity.
- `EndpointCheck`, `EndpointRules` and `LeafSafety.lean` / `CertSound.leaf_enclosures` establish each
  intermediate endpoint enclosure using only earlier established enclosures. Euclidean
  floor/ceiling and intersections are proved sound. `CertSound.Q_eq_pow` identifies
  the exact scale as 2^50 (derived/proved), so stored grid values represent multiples
  of 2^-50 (derived). The final integer margin gives a strict real bound.
- `RawLeafSound.lean` / `CertSound.RawReceipt.Valid.safe` is the complete generic receipt soundness rule.
  `Instances/` supplies its premises from the already accepted numerical receipts.
- `Parameters` and `ParamChunks` kernel-check exact frozen grid parameter correspondence.
  `FrozenLink.forward_eq` in `FrozenFunctions.lean` unfolds the actual frozen model; `FrozenEvaluation` and
  `FrozenLink.model_correspondence` in `FrozenParameters.lean` connect every real input to its scaled execution.
- `TreePilot.check_covers` in `CoverageSound.lean` proves the recursive algorithm sound. `CoverageInstance`
  proves property-root containment and terminal classification. `Final.lean` combines
  coverage, the existing box bindings and every leaf's safety theorem.

The original packed/residual/endpoint/margin acceptance modules in route-a-all were imported
as compiled oleans. They were not rebuilt. New instance work checks metadata, parameter
bindings and generic list identities. The exact frozen real statement is the theorem proved;
the specification was not weakened. No novelty claim is made.

## Timings and replay

The following successful-run counts are measured; CPU and elapsed sums are derived from
measured GNU time records. Repeated successful generic compilations/replays are included.
Failed and deliberately stopped attempts are listed separately in timing-summary.json.
Diagnostic probe timings are included; their temporary module was removed and is not
part of the delivered proof-module manifest.

| Phase | Successful runs (measured) | CPU seconds (derived) | Sum of run elapsed seconds (derived) | Peak RSS KiB (measured maximum) |
|---|---:|---:|---:|---:|
| Compilation | 136 | 4250.58 | 4271.21 | 9380784 |
| Kernel replay | 137 | 4485.66 | 4560.57 | 8786584 |

Derived launch-to-final-completion span: 4321.43 seconds,
from measured launch timestamps and elapsed durations. This includes engineering failures,
coordination gaps and overlapping work. CPU for stopped runs lacking a completed time
record is **not found**, rather than estimated or treated as zero.

Every actual Lean invocation uses systemd certcheck.slice, two configured threads,
a pinned CPU pair and MemoryMax=16G. Long coordinators also run as persistent systemd
services. Replay uses the explicit minimal `env -i` environment with only PATH (the pinned
Lean toolchain plus /usr/bin:/bin), workspace HOME and TMPDIR, LEAN_PATH and
LEAN_NUM_THREADS=2. Actual commands and GNU time data are retained in logs/*.time.
Leanchecker replays local declarations against imported modules; every new local dependency
is replayed separately. This is Lean kernel replay, not a claim of an independent kernel.

## Engineering failures and resource accounting

Early monolithic parameter checks were intentionally stopped as normalization memory
approached their cap. Small row-group modules completed instead. Two systemd stop returns
were initially logged as zero although no olean or completed time file existed; explicit
status-correction records supersede those entries. The runner now requires a fresh olean
and a completed time record before recording compile success.

An early failed adapter attempted a definitional conversion of a numerical claim. It took
117.14 seconds elapsed (measured) and was replaced by a generic slice/head identity, so the
final adapter reuses the existing margin theorem without that conversion. Other failed
compilations were proof-engineering/type elaboration attempts; none is counted as a proof.
Their logs and timings remain in runs.jsonl.

A brief early orchestration overlap occurred before per-slot locks were added. The conservative
peak of launch-to-return intervals is 5 (derived, not a sampled Lean-process count),
so this run does not claim perfect compliance with the requested concurrent-job ceiling.
The extra root job shared its already assigned CPU pair. Per-slot locks now enforce the
configured four-slot arrangement, and every job retains its two-thread pinning and memory cap.

Measured final free disk: 119844163584 bytes, above the reported
45 GB reserve. No downloads, upstream edits, paid calls or network writes were needed.
The first draft preceded the initial compilation; measured report filesystem birth time:
2026-10-24 00:53:22.373754786 +0000. Progress was checkpointed in STATUS.json after successful lemma modules.

## Artifacts

- Final.lean / Final.olean: closed frozen theorem and axiom audit.
- verification-manifest.json: every new proof module and current replay binding.
- runs.jsonl / timing-summary.json / logs/: completed attempts, corrections and timings.
- input-audit.json: original/copied specification and frozen parameter source hashes.
- STATUS.json: final completed state and lemma/module inventory.
- SHA256SUMS: sources, oleans, scripts, reports and verification records.

To replay a module with the exact pinned environment and resource wrapper, run
`python3 run.py Final --replay`; the runner records the invocation in runs.jsonl.
Re-running any wrapper updates logs/records, so regenerate SHA256SUMS afterward.

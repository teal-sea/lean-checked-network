# Whole real ACAS arithmetic proof

Status (measured): **34 / 34 leaf theorems compiled**, **966 module replays completed**. Last report update (measured UTC): 2026-10-23T21:58:08.968472+00:00. First draft was saved before builds started; measured filesystem birth time: 2026-10-23 20:49:46 UTC.

Plain answer: **Lean checked all 34 real-certificate leaves, shared setup, coverage check and the conjunction in 38.10 minutes elapsed (measured), using 3.4594 CPU-hours (derived sum of measured CPU).** The leaf data plus acceptance alone cost 3.4466 CPU-hours (derived). Parallelism was at most six jobs on twelve pinned CPUs (configured; resource samples retained). Independent kernel replay is additional and is measured separately below. These are numerical receipt acceptances, with a separate tree coverage check. Checker soundness and importer correspondence remain unproved. No novelty claim.

## Inputs and method

Toolchain: pinned Lean 4.35.0 (reported source: supplied toolchain path in the brief); exact executable paths are retained in every GNU time record and in `runner.py`.

The certificate SHA256 (measured) is `89d8742b8a08f2259dfb99f8dcac061cad9276db1fb75fb2d5a896ed89cc0b0f`; frozen Net.lean SHA256 (measured) is `4f89de9f7ca25762b638c97a51625d0c1065a0d3b5ab2ffe5de3ba7f32964426`. The exact strict threshold (reported source, preserved verbatim) is `3991125645861615/1000000000000000`.

All 34 receipts (measured count) passed the copied independent Python verifier before compilation. `input-audit.py` additionally checks leaf selection, boxes, all block weights, and frozen hashes. Weights and generic arithmetic cores are shared once. Leaf-specific dual/product literals, biases, endpoints and proof modules retain the pilot structure. Every leaf has a `Proof<id>.node<id>NC` theorem of the pilot shape. The assembly additionally checks the exact terminal-ID list and each receipt box against its coverage-tree node.

Smallest exact margin (measured receipt, independently verified): node **38**, `1211783778660853560685887064332051414124401203569759/2126764793255865396646091296448551321600000000000000`. Its decimal value **0.5697779944935675** is derived.

## Per-leaf build measurements

All entries in the following table are measured GNU time user+system CPU and measured elapsed wall time; sums are derived from measured module runs. Wall sums represent serial module time for a leaf, not total concurrent elapsed time. Peak RSS is the maximum measured process RSS within that phase. Data means literal modules and NodeData; acceptance includes packed checks, shape, residual chunks, endpoint checks, strict margin and assembly of the leaf theorem. Both phases include imports, elaboration and output. A dash means unfinished.

| Leaf | Data CPU s | Data wall s | Data peak KiB | Acceptance CPU s | Acceptance wall s | Acceptance peak KiB | Complete |
|---:|---:|---:|---:|---:|---:|---:|:---:|
| 8 | 88.07 | 83.64 | 2003020 | 313.81 | 316.92 | 4491388 | yes |
| 13 | 88.31 | 84.04 | 2002744 | 270.07 | 273.55 | 4347204 | yes |
| 17 | 87.94 | 82.96 | 2000724 | 282.92 | 285.90 | 4311744 | yes |
| 24 | 87.77 | 82.55 | 2002944 | 279.41 | 282.09 | 4342824 | yes |
| 27 | 90.60 | 85.49 | 2003660 | 272.04 | 274.31 | 4369152 | yes |
| 29 | 89.04 | 84.27 | 2003224 | 290.43 | 293.52 | 4379672 | yes |
| 30 | 91.49 | 86.38 | 2001388 | 275.26 | 285.92 | 4364964 | yes |
| 31 | 87.90 | 83.65 | 2001964 | 249.67 | 254.17 | 4290204 | yes |
| 32 | 89.45 | 84.73 | 2001544 | 297.86 | 303.85 | 4512300 | yes |
| 33 | 90.32 | 85.22 | 2001756 | 288.45 | 294.77 | 4474644 | yes |
| 34 | 87.95 | 83.27 | 2000668 | 259.77 | 265.66 | 4314256 | yes |
| 36 | 90.17 | 85.88 | 2001656 | 296.38 | 301.64 | 4449976 | yes |
| 37 | 91.08 | 88.04 | 1999844 | 258.91 | 263.74 | 4347752 | yes |
| 38 | 94.59 | 93.28 | 2001512 | 291.91 | 297.09 | 4543768 | yes |
| 39 | 94.06 | 88.67 | 2001364 | 251.26 | 253.61 | 4291760 | yes |
| 40 | 90.66 | 89.37 | 2001572 | 294.78 | 298.93 | 4507772 | yes |
| 41 | 93.89 | 92.70 | 2001712 | 280.80 | 284.39 | 4496888 | yes |
| 42 | 91.10 | 88.78 | 2002024 | 274.29 | 277.85 | 4410268 | yes |
| 46 | 89.86 | 86.90 | 2001604 | 262.61 | 266.65 | 4381444 | yes |
| 49 | 92.19 | 88.35 | 1999296 | 238.61 | 242.31 | 4343668 | yes |
| 50 | 90.36 | 86.61 | 1999176 | 246.05 | 249.36 | 4264644 | yes |
| 51 | 90.09 | 86.45 | 2001548 | 283.52 | 286.11 | 4487576 | yes |
| 52 | 92.57 | 88.63 | 2001800 | 280.58 | 283.23 | 4491736 | yes |
| 53 | 90.42 | 88.77 | 2001428 | 247.65 | 249.83 | 4377100 | yes |
| 54 | 89.01 | 84.74 | 2001196 | 257.20 | 261.02 | 4266264 | yes |
| 55 | 92.17 | 88.04 | 2001408 | 305.49 | 309.03 | 4529656 | yes |
| 56 | 91.13 | 87.08 | 2001624 | 303.60 | 308.29 | 4499264 | yes |
| 57 | 90.74 | 86.16 | 2001224 | 269.30 | 271.87 | 4331460 | yes |
| 58 | 91.86 | 88.94 | 2003944 | 301.56 | 305.26 | 4509804 | yes |
| 59 | 88.60 | 84.95 | 2001748 | 257.61 | 261.14 | 4281084 | yes |
| 63 | 89.75 | 85.69 | 2001660 | 264.91 | 267.50 | 4478900 | yes |
| 64 | 88.62 | 84.63 | 2001820 | 264.33 | 266.47 | 4481396 | yes |
| 65 | 91.23 | 85.63 | 2001668 | 258.99 | 261.20 | 4473304 | yes |
| 66 | 90.40 | 85.71 | 2001400 | 264.31 | 266.85 | 4472876 | yes |

## Totals and verification

- data: 3073.39 CPU s, 0.853719 CPU-hours (derived sums); peak 2003944 KiB (measured maximum).
- acceptance: 9334.34 CPU s, 2.592872 CPU-hours (derived sums); peak 4543768 KiB (measured maximum).
- shared: 42.96 CPU s, 0.011933 CPU-hours (derived sums); peak 6762760 KiB (measured maximum).
- assembly: 2.99 CPU s, 0.000831 CPU-hours (derived sums); peak 2275864 KiB (measured maximum).
- control: 25.22 CPU s, 0.007006 CPU-hours (derived sums); peak 3246504 KiB (measured maximum).
- replay: 10133.26 CPU s, 2.814794 CPU-hours (derived sums); peak 5866176 KiB (measured maximum).
- Build concurrent wall time: 2267.22 s (measured).
- Replay elapsed span (overlaps build): 2089.20 s (measured).

Untrusted emission: 39.595 CPU s; independent Python receipt verification: 24.493 CPU s (derived sums of measured process CPU, separately charged).

The requested resource arrangement is six Lean processes maximum, two pinned CPUs per job within CPUs 0–11, `LEAN_NUM_THREADS=2`, `OMP_NUM_THREADS=2`, and `MemoryMax=16G` for every job. A finite two-worker replay batch overlaps the final four-leaf build, on the two CPU pairs released by the build; the final replay stage starts on the other four CPU pairs, reserves that batch’s modules to prevent duplication, and expands to six workers when the batch ends. Every Lean/replay invocation runs via a separate `systemd-run --user` unit. The coordinator also runs as a persistent systemd service. No upstream edits or network writes. GNU time output is in `logs/`; `runs.jsonl` is append-only. Shared generic proof compilation is separately charged. Failed runs, if present, are separate from successful totals.

Coverage: the copied step1 `CoverageData.coverage_checked` has compiled from the same hashed certificate tree. Exact regeneration from the current hashed certificate matched this entire source byte-for-byte (measured `coverage-audit.json`), including internal nodes. It audits the outward property box, exact splits and all visited nodes. Its axiom audit reports `[propext, Classical.choice, Quot.sound]` (measured log). This is an executable coverage check; a theorem that this algorithm implies geometric coverage is not provided here.

Replay uses the route library alone in LEAN_PATH for modules whose imports are only local modules and Lean; the Mathlib-based generic soundness modules use the cached package search paths. The early replay batch retained the full cached search path. These actual costs are retained, without claiming a like-for-like speedup.

Replay: `leanchecker` replays each new module's local declarations against imported dependencies, and every new local dependency module is checked separately. It uses the explicit minimal `env -i` environment with PATH, HOME, TMPDIR, LEAN_PATH and LEAN_NUM_THREADS. This is Lean kernel replay, not a second independent kernel implementation. All 966 new compiled modules passed (measured count and zero exit codes). Each `logs/*-replay.log` identifies the replayed module; `replay-modules.json` is the full manifest.

Control engineering failure (measured): the initial changed-weight target at leaf 17 had an entirely zero dual row. Its isolated packed check remained true, so Lean correctly refused the proposed false theorem; the failed source/log/time are retained under `failed/`. The final control changes an entry whose dual row has nonzero support. This is not an accepted theorem or a semantic soundness result.

Controls: generated on different leaves: dual-entry corruption at leaf 8 and changed weight at leaf 17. The real unsafe mutation changes output-layer weight [0,25] to 1000000 (reported mutation file). `UnsafeNode13` substitutes that exact weight into the final affine coefficient while retaining the original receipt; `unsafe13_rejected` checks that the recomputed strict margin is false. Python independently rejected the stale receipt for this mutated network (measured `unsafe-python.log`). All three Lean rejection theorems passed (measured zero exit codes); logs are `ControlDual.log`, `ControlWeight.log`, and `UnsafeControl13.log` under `logs/`.

Axiom outputs: every arithmetic proof module prints its theorem axioms; logs retain the exact output. The final exact axiom output is reproduced below. No `sorryAx` or new axioms appear in these audits.

Setup diagnostic: an early bare `leanchecker --help` probe failed because `lean` was absent from PATH; no module was checked (measured error output). This is separate from module compilation/replay outcomes. All actual kernel jobs use the configured toolchain and systemd resource limits.

Remaining proof gaps: executable-list/offset correspondence to the generic packed-matrix soundness theorem; residual/telescoping composition and network semantics; a proved-sound coverage algorithm and its composition with the leaf checks; importer/model/property correspondence. Passing all numerical checks does not close those gaps.

Failed attempts (measured): `[{"module": "ControlWeight", "phase": "control", "status": 1, "cpu_s": 11.74, "wall_elapsed": 11.82185959815979, "rss_kib": 2108484.0}]`

All Lean build, control and replay stages together occupied 66.54 minutes from the first compile launch to the last replay completion (measured elapsed); combined successful-run CPU was 6.2812 CPU-hours (derived). This includes orchestration gaps and all diagnostic controls.

## Final axiom audits (measured tool output)

```text
'allLeavesNC' depends on axioms: [propext]
'terminalIds' depends on axioms: [propext]
'coverage_checked' depends on axioms: [propext, Classical.choice, Quot.sound]

'ControlDual.rejected' does not depend on any axioms

'ControlWeight.rejected' depends on axioms: [propext]

'unsafe13_rejected' depends on axioms: [propext]

```

Final free disk: **94939099136 bytes** (measured). `timing-summary.json` contains per-module CPU, GNU wall times, launch elapsed times and peak RSS; its per-leaf phase summaries include replay. The build concurrent wall time above includes one-time cores and coverage; the full-check headline also includes the final conjunction and its box/terminal bindings. Replay and diagnostic controls are excluded from the headline and charged separately. `SHA256SUMS` binds all Lean sources, Python/shell generators, receipts, measurements and reports; `input-hashes.json` binds external inputs.

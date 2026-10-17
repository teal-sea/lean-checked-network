# Transformer lane: status of the combined branch

Two retained branches, merged unchanged onto main 3fdba53: `claude/transformer` (design, training,
core-Lean model `lean/`) and `claude/transformer-mathlib` (`mathlib/`). Two toolchains, two Lake
projects: `lean/` is Lean v4.35.0-rc2 with no Mathlib, `mathlib/` is v4.35.0 with Mathlib v4.35.0.
`mathlib/TransformerBridge` now joins them (see below).

| Claim | Status |
| --- | --- |
| Python simulation of the packed program: 12,769 pairs, 0 mismatches (`lean/logs/simulate_fast_program.log`) | **measured**, not a kernel build |
| `lean/`: Model, Fast, Equiv (`fastCheck_correct`) compile | **evidenced** in run 38997742989 at d348af0 (job 117294729862), which reached row0 |
| `lean/`: split `tables_ok` kernel-checked | **measured** in run 38997742989 at d348af0: all 12 bound component modules compiled (peak component 2.17 GiB); exact `tables_ok` assembled in 0.64 s, maxRSS 719764 KiB. Frozen data hashes/emission tests passed |
| `lean/`: row 0 (`fast_0`) kernel-checked | **unproved**: timed out (exit 124) after 20 minutes in that run; about 4605 MiB Lean RSS, zero swap, about 10.9 GB available. No accepted row0 verdict. This was not the previous table-validation memory failure |
| `lean/`: fixed pairs (0,0), (0,112), (96,73) | **source only, no kernel result yet**. CI core now runs a PAIR PILOT, 300 s per pair, two threads maximum. Green pilot does not establish row0 or all-input acceptance |
| `mathlib/`: exp bound, logit perturbation, raw-model identity | retained logs say built and replayed; job `mathlib` re-runs `verify.sh` from the Mathlib cache |
| Theorem C (`real_model_adds_mod_113`, `_raw`) | **conditional**, not unconditional |

## Table bounds, split (kernel-checked in run 38997742989)

`Net.tables_ok : tablesOk tab bnd = true` keeps its statement and `tablesOk`/`bnd`/`fastCheck_correct` are untouched. The proof is now
`tablesOk_of` (`Transformer/BoundsLib.lean`, an ordinary proof over arbitrary `T`, `bd`, so nothing is evaluated while assembling) applied to
the fifteen conjuncts, each built from `ok_<vector> : vecOk n k <vector> = true := by decide +kernel`, one per table vector
(2,346 in all: 1,824 head vectors, 8 `TI2`/`TU2`, `CI`, `CU`, 512 rows of `G`; in `Net/B/*.lean`, one module per data file). `gen_lean_transformer.py` emits them (`--bounds-only` rewrites the
bounds layer from the committed data; `Net/W.sha256` pins the numeric data, which is byte-identical to the previous commit).
`smoke.sh` builds one representative slice first (`Net.B.TI0_0`, 114 vectors, a ninth of the table), then the rest serially, `Table`, and `Cols`. The default `CORE_MODE=pair-pilot` builds three independent literal-pair modules; `CORE_MODE=full-row` retains the explicit row0 route.
`Net/Cols.lean` adds kernel column-sum certificates `colAbsSum tab.G k <= 8774 * 2025` for the 113 columns of `G` (`colSums_ok`); it is about the core list
table only, and its link to the Mathlib `Tables.Bounded` (`hB`) is **not proved**. A Python mirror (`lean/mirror_bounds.py`, not kernel evidence) finds
every vector within `bnd` and a maximum column sum of 5,793,793.

## Bridge (source written, not yet kernel-checked)

`mathlib/TransformerCore/{Model,Fast,Equiv}.lean` are mechanical copies of `lean/Transformer/*` with the word `Transformer`
renamed to `TransformerCore` (`mathlib/sync_core.sh`, `--check` is a CI gate). `mathlib/TransformerBridge/Bridge.lean` proves,
for a list-based `T : Tab` read as Fin-indexed tables (`toTables`) and the core configuration `cfgOf chosen 256`:
`expFix_eq`, `logits_nth_eq` (entry `k` of the core `logits` is `Transformer.intLogits`), and
`hA_of_fastCheck` (a passing `fastCheck` at `(a, b)` gives the `hA` inequality on that pair, using `fastCheck_correct`).
CI job `bridge` builds it. Compiler-informed repairs are retained in this worktree but have not been compiled after the edits; a fresh successful build/replay is still required.

## Unclosed obligations (Theorem C stays conditional on these)

- `hA` for the trained literals: needs `fastCheck` on all 12,769 pairs (`Net/AllInputs.lean`, not built) and the `Net` data inside
  the Mathlib project (copy of `lean/Transformer/Net` under the same rename), plus `cfg = cfgOf chosen 256` and `tab.G.length = 512` by `decide`.
- `hB`: `Tables.Bounded chosenBounds` from `tablesOk` for TI, TU, CI, CU (entry bounds are below `chosenBounds`), and the column sums of `G`
  (`sum_i |G i k| <= 8774 * 2025 = 17,767,350`): `tablesOk` only gives the per-entry bound 35,663, and 512 * 35,663 exceeds 17,767,350.
  `Net/Cols.lean` supplies the column sums as kernel certificates over the core list table once its build is green; the proof that this
  gives `Tables.Bounded` for `toTables tab` (a Fin-indexed sum, per-head TI/TU bounds) is still to write.
- `hT`: `toTables tab = rawTables 256 W` for the exact quantised matrices. Not proved; `toTables` was written to match `rawTables` (position 2 at token 113 only).
- The core lane has never completed row 0 (see `END-TO-END.md` in the artifacts for the diagnosis of run 38994712205).
- Nothing here concerns the original floating-point checkpoint.

## What CI runs

- `mathlib`: `lake exe cache get`, `transformer/mathlib/verify.sh` (one module per `lake` call,
  `LEAN_NUM_THREADS=2`, source scan, leanchecker replay, axiom check). Artifact `transformer-mathlib-verify`.
- `core` (**PAIR PILOT**, `CORE_MODE=pair-pilot`): `transformer/lean/smoke.sh` builds core, split bounds, `Net.Table`, `Net.Cols`, then independent `Net.Pair0_0`, `Net.Pair0_112`, `Net.Pair96_73` modules. Each theorem is exactly `fastCheck cfg tab bnd E2 a b = true := by decide +kernel`, importing the unchanged `Weights`. Each pair build and replay has its own 300 s timeout, log and GNU time wall/maxRSS file; any failure stops the run. At most two Lean threads. Source scan, seven standard-axiom checks (core correctness, tables, two Cols theorems, three pilots), and Equiv/Table/Cols/pair leanchecker replay gate success. Artifact: `transformer-core-pair-pilot`, including `ci-out/STATUS.txt`. **Pilot success leaves row0 and all-input acceptance unproved.** No throughput claim exists before actual CI output.
- The later full-row route remains `CORE_MODE=full-row LEAN_NUM_THREADS=2 ./smoke.sh` in `transformer/lean`; it builds/replays `Rows00` with the retained 1200 s limit instead of the pair modules. It does not build rows 1..112 or `AllInputs`. Do not rerun this route until pair measurements justify it.

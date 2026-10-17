# Transformer lane: status of the combined branch

Two retained branches, merged unchanged onto main 3fdba53: `claude/transformer` (design, training,
core-Lean model `lean/`) and `claude/transformer-mathlib` (`mathlib/`). Two toolchains, two Lake
projects: `lean/` is Lean v4.35.0-rc2 with no Mathlib, `mathlib/` is v4.35.0 with Mathlib v4.35.0.
Nothing joins them yet.

| Claim | Status |
| --- | --- |
| Python simulation of the packed program: 12,769 pairs, 0 mismatches (`lean/logs/simulate_fast_program.log`) | **measured**, not a kernel build |
| `lean/`: Model, Fast, Equiv (`fastCheck_correct`) compile | **not yet evidenced** by any build record on GitHub; `.github/workflows/transformer.yml` job `core` is the first |
| `lean/`: `tables_ok` and row 0 (`fast_0`) kernel-checked | **not yet evidenced**; same job. Rows 1 to 112 and `Net/AllInputs.lean` are **deliberately not built** until row-0 time and memory are measured |
| `mathlib/`: exp bound, logit perturbation, raw-model identity | retained logs say built and replayed; job `mathlib` re-runs `verify.sh` from the Mathlib cache |
| Theorem C (`real_model_adds_mod_113`, `_raw`) | **conditional**, not unconditional |

## Unclosed bridge obligations (Theorem C stays conditional on these)

- `hA`: integer all-input margin, i.e. on each of the 12,769 pairs `intLogits chosen T 256 a b` has its
  right logit above every other by more than the bound. Not proved for the trained literals.
- `hB`: `T.Bounded chosenBounds`, the table-entry bounds, not proved for the trained literals.
- `hT`: for the raw model, `T = W.rawTables 256` with the quantised matrices. Not proved.
- No link between `intLogits` (mathlib) and the packed program `fastCheck` (core); the balanced-digit
  unpacking lemma for signed entries is not written. The two projects cannot import each other.
- The Lean `expFix` agrees with the Python `expfix` on 12 inputs (measured), not proved.

## What CI runs

- `mathlib`: `lake exe cache get`, `transformer/mathlib/verify.sh` (one module per `lake` call,
  `LEAN_NUM_THREADS=2`, source scan, leanchecker replay, axiom check). Artifact `transformer-mathlib-verify`.
- `core`: `transformer/lean/smoke.sh`: `lake build Transformer`, `lake build Transformer.Net.Rows00`,
  source scan, axioms of `fastCheck_correct`, `tables_ok`, `fast_0`, leanchecker replay of Equiv (gating) and
  Rows00 (recorded). Time and peak RSS per step in artifact `transformer-core-smoke`.

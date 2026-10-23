# Whole-head Kronecker checks for the `TI` and `TU` tables

Written 2026-10-22. This note explains `TransformerBridge/Kronecker/`. Those modules prove that the frozen `TI` and `TU` tables equal the tables computed from the raw integer weights, for all four heads, all three positions and all 114 tokens. Their pieces feed `TransformerBridge/FinalRaw.lean`, which states the unconditional raw-model theorem.

Status words follow the house rule: **proved** (kernel-accepted, replayed by `leanchecker`, standard axioms), **measured**, **derived**, **open**.

## The obligation

From `Transformer/Raw.lean`, for head `h`, position `j` and token `tk`:

```
xhat tk j d   = tok tk d + pos j d                          d : Fin 128
vvec h tk j l = Σ_d xhat tk j d · WV h d l                   l : Fin 32
ovec h tk j d = Σ_l vvec h tk j l · WO h l d                 d : Fin 128
TI h j tk i   = if j = 2 ∧ tk ≠ 113 then 0 else Σ_d ovec h tk j d · Win d i     i : Fin 512
TU h j tk k   = the same with U d k                                              k : Fin 113
```

There are 4 heads × 229 active (position, token) slots, so 916 vectors of width 512 and 916 of width 113. Every step above is exact integer arithmetic, with no rounding between `vvec`, `ovec` and `Win`/`U`.

The earlier route certified one slot at a time, and five slots were accepted that way. **Measured** on the project host: about 370 s of two-thread Lean proof compilation per slot, excluding audits, packaging and the per-token basis certificates. **Derived:** extrapolating that compile time to all 916 slots gives roughly 94 hours. That figure is an estimate; the full per-slot run was never attempted.

## The idea

Prove heads, not slots. `Kronecker.Core` defines one Boolean program, `headCheck`, which the kernel runs directly on the lists that define the raw weights (`RawPackedPilot.Data.tok`, `pos`, `WV`, `WO`, `Win`, `U`) and on the frozen table rows. Inside it, whole rows are packed into single natural numbers in a power-of-two base chosen from checked bounds, `B = 2^47` for `TI` and `B = 2^46` for `TU` (Kronecker substitution). A matrix product then becomes a few hundred thousand GMP multiply-adds, which the kernel performs natively. `Kronecker.Spec` proves once, for every head and both fields, what a passing check means.

## What the kernel computes (`Kronecker.Core`)

For head `h` and output matrix `Mout` (`Win` with `n = 512`, or `U` with `n = 113`):

1. **Pack the output matrix by columns.** `PW_d = Σ_i Mout_{d,i} Bⁱ` for each of the 128 rows `d`. Entries are packed as offset digits `x + c ≥ 0` on `Nat`, one GMP operation each (`colpkN`); the offset is removed afterwards (`unoff`).
2. **Push the packed columns back through the head.** `PM_l = Σ_d WO_{h,l,d} PW_d`, then `R_e = Σ_l WV_{h,e,l} PM_l` (`vecmat` twice). Each `R_e` packs the whole contribution of input coordinate `e` to a table row.
3. **One packed value per slot.** The packed value of slot `(j, tk)` is `Σ_e (tok_{tk,e} + pos_{j,e}) R_e`. The position part is computed once per position and reused for all 114 tokens.
4. **Compare with the frozen row.** The frozen row `F` is packed with offset `K` (`pkN`), and the check is `pkN B K F = dot(tok_tk, R) + p_j + K·Σ_{i<n} Bⁱ`.
5. **Check shapes and bounds in the same pass.** This covers the token, position and output-matrix shapes, the lengths of the selected `WV`/`WO` slices and of the frozen rows, the entry bounds `Kt, Kp, Kv, Ko, Kw` on the inputs and `K` on the frozen entries, and `128·Kw·32·Ko·128·(Kt+Kp)·Kv ≤ K`, `2K < B`, `2 ≤ B` (`paramsOk`, `inputsOk`). The inner widths of the `WV`/`WO` rows are not checked. Their entries are read with the raw model's zero-default list access, and only the contracted coordinates contribute.

## Why a passing check proves the table (`Kronecker.Spec`)

`field_of_check` combines four facts:

1. **List semantics.** Each program agrees with its `nth`-indexed meaning (`nth_vecmat`, `dot_eq`, `nth_colpkN`, `pkN_spec`), and offset digits are exact under the checked bounds (`dig_spec`).
2. **Linearity.** Signed packing is linear. Three sum exchanges (`sum_input_through_value`, `sum_value_through_output`, `sum_output_through_pack`) show the packed slot value equals `Σ_i (Σ_d ovec · Mout_{d,i}) Bⁱ`. This is an identity of integers, so no carry argument is needed.
3. **Bounds.** The checked input bounds give `|Σ_d ovec · Mout_{d,i}| ≤ K` (`ovec_mul_bound`), and the frozen entries are checked to lie in `[-K, K]`.
4. **Uniqueness of balanced digits** (`packed_inj`). If `2K < B`, two digit vectors with entries in `[-K, K]` and the same base-`B` value are equal entrywise. So one packed equality forces all 512 (or 113) entries to agree.

`TI_head_of_check` and `TU_head_of_check` restate this as `(toTables T).TI h j tk = (W.rawTables S).TI h j tk` for every `j`, `tk` and `S`. The unused slots `j = 2, tk ≠ 113` are `0` on both sides by definition. `RawPackedPilot.weights` reads the same lists, so the five data bridges are `rfl`.

## The modules

| module | content |
|---|---|
| `Kronecker.Core` | the checker `headCheck` and its list programs (definitions only) |
| `Kronecker.Spec` | `field_of_check`, `TI_head_of_check`, `TU_head_of_check` and their lemmas |
| `Kronecker.Heads.CheckTI{h}`, `CheckTU{h}` | `checkTI{h} : headCheck … = true := by decide +kernel`, one per head and field |
| `Kronecker.Heads.TI{h}`, `TU{h}` | `TI_head{h}_eq : (toTables Net.tab).TI h = (weights.rawTables 256).TI h`, and the same for `TU` |
| `Kronecker.Fields` | `TI_eq` and `TU_eq`: the full fields, all four heads |
| `FinalRaw` | `tables_eq_raw` (`hT`), `margin_all_pairs` (`hA`), `raw_model_adds_mod_113` |

The 17 `Heads` and `Fields` modules are generated by `kronecker_generate.py` (standard library only) from `runs/best.npz` and the frozen tables, each pinned by a committed sha256. `python3 kronecker_generate.py --check` regenerates them and compares byte for byte. `test_kronecker.py` holds 25 tests.

Bounds used, chosen from each head's data and re-checked by the kernel:

| head | field | B | K | Kt | Kp | Kv | Ko | Kw |
|---|---|---|---|---|---|---|---|---|
| 0 | TI | 2^47 | 49761849704448 | 68 | 59 | 98 | 93 | 82 |
| 0 | TU | 2^46 | 22453517549568 | 68 | 59 | 98 | 93 | 37 |
| 1 | TI | 2^47 | 50679118823424 | 68 | 59 | 102 | 91 | 82 |
| 1 | TU | 2^46 | 22867407273984 | 68 | 59 | 102 | 91 | 37 |
| 2 | TI | 2^47 | 42259898695680 | 68 | 59 | 86 | 90 | 82 |
| 2 | TU | 2^46 | 19068490874880 | 68 | 59 | 86 | 90 | 37 |
| 3 | TI | 2^47 | 53824041517056 | 68 | 59 | 106 | 93 | 82 |
| 3 | TU | 2^46 | 24286457757696 | 68 | 59 | 106 | 93 | 37 |

The largest packed number is about 512 × 47 bits (3 KB), far below the kernel's 128 MB numeral limit.

## Cost

**Measured** on the project host, Lean v4.35.0, two threads per process, for all four heads and both fields together:

| step | modules | total wall | per module | peak RSS |
|---|---|---|---|---|
| compile | 17 | 200 s | 7 to 24 s | 6.7 GiB |
| `leanchecker` replay | 17 | 322 s | 13 to 33 s | 6.2 GiB |
| negative controls | 8 | 220 s | 17 to 38 s | 2.9 GiB |

These are pre-release measurements; the three steps were run separately and are not one elapsed pipeline. The comparison with the per-slot route is against the derived 94-hour estimate above. For the released module names, the 20 `leanchecker` replays summed to about 405 s of sequential wall time on the same host while it carried unrelated load; the release compilation steps overlapped, so their durations are not an elapsed time.

Three implementation choices mattered as much as the mathematics.

1. **Let the kernel read the original data.** An earlier version emitted claimed packed literals and bridged them back to the lists with per-entry reads. Its arithmetic took seconds, but the bridging took 422 to 605 s per 32 weight rows. Packing inside the kernel removed that cost.
2. **Use offset digits on `Nat` for every per-entry pass.** Kernel probes on real-shaped data: packing `Win` by columns took 4.1 s as `Nat` digits against 22.3 s as signed `Int`; packing 114 frozen rows took 3.9 s against 11 to 13 s.
3. **Write the programs as direct `List.rec` terms marked `noncomputable`,** so the kernel only reduces them and nothing is compiled or evaluated outside it.

## Evidence

- **Proved:** compile and `leanchecker` replay of all 20 new modules, and an exact axiom audit of every new declaration and of `raw_model_adds_mod_113` (only `propext`, `Classical.choice`, `Quot.sound`).
- **Negative controls:** in each head, one learned `Win` weight raised by 1, and separately one frozen `TI` entry raised by 1. A further control raises one `Win` weight by 1 against the frozen `CI` table. All 9 fail with exactly one kernel `decide … is false` error, and their unchanged twins compile.
- **Separately implemented checker (supporting evidence):** `nanoda_bin` 0.4.19, a type checker written independently in Rust, reported no type-checking errors for an export of an earlier, pre-rename assembly: 82,927 declarations for the final theorem and 3,940 for the head-0 `TI` certificate. Each run also reported one error from its axiom pretty-printer. These runs support the earlier assembly; they are not a re-check of the released objects, and the released theorem's axioms are established by the Lean audit above.
- **Release asset:** `transformer-final-raw-evidence` carries every compiled object and source in the theorem's project closure (2,141 modules). Its `verify.sh` authenticates the files, checks that the released theorem term proves the stated proposition, audits the axioms, replays the kernel, and optionally runs the controls.

## Scope and prior work

The method applies when a frozen table must equal an exact integer computation made of linear maps, and the inputs are data the kernel can traverse. It does not cover nonlinear stages (softmax, ReLU, rounding), which this project proves separately, and it says nothing about the floating-point checkpoint.

**Prior work:**
- The ingredients are standard: Kronecker substitution, deterministic matrix-product verification with a fixed power vector, proof by reflection, and the kernel's GMP-backed `Nat`.
- Naughton's [certified-grokking](https://github.com/brian-naughton/certified-grokking) certifies all 12,769 inputs of the exact-real model defined by Nanda et al.'s published float32 checkpoint, using trusted Python interval arithmetic, and separately proves the ideal clock decoder in Lean. It does not certify PyTorch's floating-point operational semantics. Our theorem concerns this project's frozen quantised integer model, not that checkpoint.
- Gross's [neural-net-coq-interp](https://github.com/JasonGross/neural-net-coq-interp/tree/54ff8507f5328c116fe08b7846f0c6d4e4714273) contains Coq proofs of enumerated-domain accuracy for trained max-of-two transformers, using floating-point definitions and `vm_compute` ([brute-force theorem](https://github.com/JasonGross/neural-net-coq-interp/blob/54ff8507f5328c116fe08b7846f0c6d4e4714273/theories/MaxOfTwoNumbers/Theorems/Attempt_01_BruteForce.v#L11-L30); the [simpler example](https://github.com/JasonGross/neural-net-coq-interp/blob/54ff8507f5328c116fe08b7846f0c6d4e4714273/theories/MaxOfTwoNumbersSimpler/Theorems/Attempt_01_BruteForce.v#L11-L27) reaches perfect accuracy). This is prior proof-assistant verification of transformer performance, not the same exact-integer, real-softmax theorem.

The contribution here is the combination: an unconditional theorem against frozen raw integer weights, certificates evaluated by the Lean kernel itself, and the whole-head packed table-correspondence check. We make no priority claim for the standard ingredients or for transformer verification in general.

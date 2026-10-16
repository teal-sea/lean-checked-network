# The exp bound and the logit perturbation lemma, on Mathlib

Written 2026-10-16. This Lake project holds the Mathlib half of the chain described in
`transformer/DESIGN.md` (the design lane's branch): Theorem B1 (the integer exponential `expFix` is
within `delta` of `2^f exp(x / 2^t)`), Theorem B2 (two runs of the integer program whose attention
weights differ by at most `delta` have logits within `E` of each other), the identity between the
real-exp run of the program and the real-softmax model `M_q`, and Theorem C (`M_q` answers
`(a + b) % 113` on every pair) with the brute-force facts of Theorem A taken as explicit hypotheses.
No Theorem A is proved here: the kernel check of the 12,769 pairs is the core-Lean lane's work, and
this README says at the end exactly what is needed to make Theorem C unconditional.

Status words follow the house rule: **proved** (a theorem in Lean, kernel-accepted, replayed by
`leanchecker`, standard axioms), **measured** (a computation, in Lean's `#eval` or in Python),
**derived** (a pencil argument, not in Lean), **open**.

Toolchain: `leanprover/lean4:v4.35.0` with Mathlib tag `v4.35.0` (commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`), the same `lakefile.toml` and `lake-manifest.json` as
`phasegrid/mathlib`; the Mathlib oleans were taken from the phasegrid stage 2 build (hard links, no
download, nothing compiled from source; `lake build` reports `9047` jobs for the first module, all
but one of them Mathlib's cached oleans).

## Files

| Path | What it is |
| --- | --- |
| `Transformer/ExpFix.lean` | `expFix`, `deltaBound`, Theorem B1 (`expFix_close`) and its instance at the chosen parameters (`expFix_close_chosen`, bound `2`) |
| `Transformer/Program.lean` | the tables, the per-pair program as a function of the twelve attention weights over any ordered commutative ring (`logits`), its integer and real-exp instances (`intLogits`, `realExpLogits`), the cast lemma, `argmaxFirst` (first index on a tie) |
| `Transformer/Logits.lean` | the bound constants (`Ebound`), the design's `E` as a checked literal (`Ebound_chosen`), Theorem B2 (`logits_close`), the margin corollary (`strict_max_of_margin`) |
| `Transformer/Compose.lean` | `M_q` through the tables (`mq`), the identity `L* = D* S^6 mq` (`realExp_eq_mq`), Theorem C with hypotheses (`real_model_adds_mod_113`, `real_model_adds_mod_113_chosen`) |
| `Transformer/Raw.lean` | the raw integer matrices (`Weights`), `rawTables` (what `build_tables` computes), the real-softmax transformer `model` from the raw matrices, `model_eq_mq`, Theorem C for `model` (`real_model_adds_mod_113_raw`, `_chosen`) |
| `verify.sh`, `verify.out` | build one module per `lake` call under the shared lock, source scan, `leanchecker` replay of every module, `#print axioms` on every theorem (`axioms_all.lean`, `axioms_all.out`) |
| `eval_check.lean`, `eval_check.out`, `check_expfix.py`, `check_expfix.out` | `#eval` of the Lean `expFix` against `int_transformer.py`'s `expfix` on 12 inputs (measured) |

## The definitions

`expFix` (`ExpFix.lean`), for parameters `p = (t, f, n, m, R)` and an integer `x`:

    coeff p i   = (n-1)! / i! * 2^((t+m)(n-1-i))                  (natural numbers; the division is exact for i < n)
    coeffs p    = [coeff p 0, ..., coeff p (n-1)]
    horner [c0, c1, ...] x = c0 + x * horner [c1, ...] x          (so horner (coeffs p) x = sum_{i<n} c_i x^i, an integer)
    bigF p      = (n-1)! * 2^((t+m)(n-1))
    expFix p x  = if x < -(R * 2^t) then 0
                  else 2^f * (horner (coeffs p) x).natAbs ^ (2^m) / bigF p ^ (2^m)     (natural-number division)

This is `expfix` of `int_transformer.py` (Horner from `i = n-1` down to `0`, one floor at the end,
the power taken on `|N|`, which equals `N^(2^m)` because `2^m` is even). Measured: `eval_check.out`
and `check_expfix.out` agree on all 12 inputs `0, -1, -2, -12345, -2^31, -2^32, -3 2^32,
-(24 2^32 - 1), -(24 2^32), -(24 2^32 + 1), -100 2^32, -1234567890123` at the chosen parameters
(values `4294967296, 4294967295, 4294967294, 4294954951, 2605029347, 1580030168, 213833830, 0, 0, 0, 0, 0`),
on the 16 coefficients and on `bigF`. `chosen = (32, 32, 16, 5, 24)`.

The program (`Program.lean`), DESIGN.md section 6, over a type `alpha` with `[CommRing alpha] [LinearOrder alpha]`
and attention weights `e : Fin 4 -> Fin 3 -> alpha`:

    Dh e h      = sum_j e h j
    Dprod e     = Dh e 0 * Dh e 1 * Dh e 2 * Dh e 3
    cof e h     = the product of the other three Dh                        (cof e h * Dh e h = Dprod e, proved: cof_mul_Dh)
    att e t     = sum_h cof e h * sum_j e h j * t h j
    pre T tok e i      = Dprod e * CI i + att e (fun h j => TI h j (tok j) i)
    hid T tok e i      = max 0 (pre T tok e i)
    logits T S tok e k = Dprod e * CU k + S^2 * att e (fun h j => TU h j (tok j) k) + sum_i hid T tok e i * G i k

with `tok = toks a b = [a, b, 113]`, `smax T tok h = max (max s_0 s_1) s_2` of `s_j = sc h j (tok j)`,
`shifted T tok h j = s_j - smax`, `eInt p T tok h j = expFix p (shifted T tok h j)` (as an integer),
`eReal p T tok h j = 2^f * exp (shifted T tok h j / 2^t)`, `intLogits p T S a b = logits T S tok (eInt ..)`
on the integers and `realExpLogits p T S a b = logits T S tok (eReal ..)` on the reals. `logits_cast`
(proved) says the integer run cast to the reals is the real program on the cast weights. `ans a b = a + b`
in `Fin 113`, whose value is `(a + b) % 113` (`ans_val`). `argmaxFirst L` scans the indices in order and
moves only on a strict increase, the rule of `argmax` in `lean/LeanCheckedNetwork/Network.lean`;
`argmaxFirst_eq` (proved): a strict maximum at `r` gives `argmaxFirst L = r`.

`M_q` (`Compose.lean`), the quantised model through the tables, DESIGN.md sections 2, 3 and 6 with the
scales divided out:

    softmaxW T t tok h j = exp (sc h j (tok j) / 2^t) / sum_j' exp (sc h j' (tok j') / 2^t)
    mqPre T S t tok i    = CI i / S^4 + (sum_h sum_j softmaxW h j * TI h j (tok j) i) / S^4
    mqHid                = max 0 mqPre
    mqLogits T S t tok k = CU k / S^6 + (sum_h sum_j softmaxW h j * TU h j (tok j) k) / S^4 + (sum_i mqHid i * G i k) / S^2
    mq T S t a b         = mqLogits T S t (toks a b)

`model` (`Raw.lean`), the same model from the raw integer matrices `W : Weights` (`tok`, `pos`, `WQ`,
`WK`, `WV`, `WO`, `Win`, `bin`, `Wout`, `bout`, `U`), as the ordinary real transformer with weights
`W / S` (biases `/ S^4`, `/ S^5`): `x_j = (tok[tok_j] + pos[j]) / S`, `q = (WQ/S)^T x_2`, `k_j = (WK/S)^T x_j`,
score `q . k_j` (no further `1/sqrt 32`, `WQ` carries it), softmax over the three positions,
`v_j = (WV/S)^T x_j`, head output `(WO/S)^T sum_j p_j v_j`, residual `x_2 + sum_h head_h`, `pre = (Win/S)^T r + bin/S^4`,
ReLU, `o = (Wout/S)^T m + bout/S^5`, logits `(U/S)^T (r + o)`. `rawTables W S` is `build_tables` of
`int_transformer.py` on the same matrices: `sc h j tk = q^h . (WK^h x_j(tk))`, `TI h j tk = (WO^h WV^h x_j(tk)) @ Win`,
`TU` likewise with `U`, `CI = S^2 x_2 @ Win + bin`, `CU = S^4 x_2 @ U + bout @ U`, `G = Wout @ U`, with
position 2 filled at token 113 only (zero elsewhere, never read).

## What is proved

Every theorem below prints `[propext, Classical.choice, Quot.sound]` or a subset (`axioms_all.out`:
64 of 64, `ans_val` uses no axiom); every module replayed by `leanchecker` (`replay.out`: 5 of 5 OK);
the source scan for `sorry`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern`,
`skipKernelTC` finds none (`verify.out`).

| Name | Statement (one line) | File |
| --- | --- | --- |
| `horner_map_range`, `coeff_div_bigF`, `horner_div_bigF` | `horner (coeffs p) x / bigF p = sum_{i<n} (x / 2^(t+m))^i / i!` exactly, in the reals | `ExpFix.lean` |
| `abs_pow_sub_pow_le` | `abs a <= M`, `abs b <= M`, `abs (a - b) <= eps` give `abs (a^(j+1) - b^(j+1)) <= (j+1) eps M^j` | `ExpFix.lean` |
| `natDiv_close` | a natural-number quotient is within less than `1` below the real quotient | `ExpFix.lean` |
| `expFix_close` (**Theorem B1**) | `0 < n`, `0 < m`, `R <= 2^m`, `2^f <= exp R`: for every integer `x <= 0`, `abs (expFix p x - 2^f exp (x / 2^t)) <= deltaBound p`, with `deltaBound p = 2^f 2^m tau (1 + tau)^(2^m - 1) + 1`, `tau = (n+1) / (n! n)` | `ExpFix.lean` |
| `clamp_chosen` | `2^32 <= exp 24`, from `Real.exp_one_gt_d9` (`2.7182818283^24 = 2.6489e10 > 2^32 = 4.295e9`) | `ExpFix.lean` |
| `deltaBound_chosen` | `deltaBound chosen <= 2` (the exact value is `1.00697941760`, `delta_bound` in `int_transformer.py`; `norm_num` evaluates the rational `(1 + tau)^31` exactly) | `ExpFix.lean` |
| `expFix_close_chosen` | for every integer `x <= 0`, `abs (expFix chosen x - 2^32 exp (x / 2^32)) <= 2` | `ExpFix.lean` |
| `expFix_le`, `realExp_bounds` | `expFix p x <= 2^f + deltaBound p`; `0 <= 2^f exp (x/2^t) <= 2^f` for `x <= 0` | `ExpFix.lean` |
| `cof_mul_Dh`, `logits_cast`, `sc_le_smax`, `shifted_nonpos`, `ans_val`, `argmaxFrom_stay`, `argmaxFrom_eq_of_mem`, `argmaxFirst_eq` | the program's bookkeeping, listed above | `Program.lean` |
| `Ebound_chosen` | `Ebound 256 32 2 chosenBounds = 416063585574805997938804232439435952711840399411200` (the design's `E`, 169 bits) | `Logits.lean` |
| `abs_prod3_sub_le`, `abs_prod4_sub_le` | `abs (a1 a2 a3 - b1 b2 b3) <= 3 eps M^2`, `abs (a1 a2 a3 a4 - b1 b2 b3 b4) <= 4 eps M^3` for factors bounded by `M` and differing by `eps` | `Logits.lean` |
| `Dh_abs_le`, `Dh_sub_le`, `Dprod_sub_le`, `cof_abs_le`, `cof_sub_le`, `wsum_abs_le`, `wsum_sub_le`, `att_sub_le` | the chain of DESIGN.md section 5, one line each: `abs (D^h) <= 3 Me`, `abs (D^h - D'^h) <= 3 delta`, `abs (D - D') <= 4 (3 delta) (3 Me)^3`, `abs (c^h) <= (3 Me)^3`, `abs (c^h - c'^h) <= 3 (3 delta) (3 Me)^2`, the attention term's change against a slice bounded by `B_h` | `Logits.lean` |
| `logits_close` (**Theorem B2**) | tables bounded by `B`, weights `e`, `e'` with `abs e, abs e' <= Me f delta = 2^f + delta` and `abs (e - e') <= delta`: for every `k`, `abs (logits T S tok e k - logits T S tok e' k) <= Ebound S f delta B` | `Logits.lean` |
| `strict_max_of_margin` | integer logits `L` with `L k + 2 E < L r` for every `k /= r`, real logits `L'` within `E` of `L`: `L' k < L' r` for every `k /= r` | `Logits.lean` |
| `eReal_div_Dh`, `cof_mul_eReal`, `att_eReal`, `pre_eReal`, `hid_eReal`, `realExp_eq_mq` | `e*_j / D*^h = softmaxW h j`; `c*^h e*_j = D* softmaxW h j`; the real-exp run satisfies `pre* = D* S^4 mqPre`, `hid* = D* S^4 mqHid`, `logits* = D* S^6 mqLogits`, with `D* = Dprod (eReal ..) > 0` (`Dprod_eReal_pos`) | `Compose.lean` |
| `real_model_adds_mod_113` (**Theorem C, conditional**) | see below | `Compose.lean` |
| `real_model_adds_mod_113_chosen` | the same at `chosen`, `delta = 2`, `S = 256`, `chosenBounds`, `E` the literal | `Compose.lean` |
| `rq_eq`, `rk_eq`, `rv_eq`, `rscore_eq`, `rhead_eq`, `rsoftmax_eq`, `resid_dot`, `rpre_eq`, `rhid_eq`, `rout_dot`, `rlogits_eq`, `model_eq_mq` | the raw model equals `mq (rawTables W S)` when `S^4 = 2^t`: `model W S a b = mq (rawTables W S) S t a b` | `Raw.lean` |
| `real_model_adds_mod_113_raw`, `real_model_adds_mod_113_raw_chosen` | Theorem C for the raw model, with the extra hypothesis `T = rawTables W S` | `Raw.lean` |

The exact statement of `real_model_adds_mod_113` (`Compose.lean`):

    theorem real_model_adds_mod_113
        (p : ExpParams) (hn : 0 < p.n) (hm : 0 < p.m) (hR : p.R ≤ 2 ^ p.m)
        (hclamp : (2 : ℝ) ^ p.f ≤ Real.exp p.R)
        (δ : ℕ) (hδ : deltaBound p ≤ δ)
        (T : Tables) (B : Bounds) (hB : T.Bounded B) (S : ℕ) (hS : 0 < S)
        (hA : ∀ a b : Fin 113, ∀ k, k ≠ ans a b →
          intLogits p T S a b k + 2 * (Ebound S p.f δ B : ℤ) < intLogits p T S a b (ans a b)) :
        ∀ a b : Fin 113,
          (∀ k, k ≠ ans a b → mq T S p.t a b k < mq T S p.t a b (ans a b)) ∧
            argmaxFirst (mq T S p.t a b) = ans a b

`T.Bounded B` is the conjunction `(∀ h j tok i, |TI h j tok i| ≤ B.TI h) ∧ (∀ h j tok k, |TU h j tok k| ≤ B.TU h) ∧
(∀ i, |CI i| ≤ B.CI) ∧ (∀ k, |CU k| ≤ B.CU) ∧ (∀ k, ∑ i, |G i k| ≤ B.G)`, and `hA` is Theorem A in one line:
on every pair the integer program's logit at `(a + b) % 113` exceeds every other logit by more than
`2 Ebound` (that is `answer = (a + b) % 113` and `margin > 2E` together). The version for the raw model
(`Raw.lean`) adds `(hSt : (S : ℝ) ^ 4 = 2 ^ p.t)` and `(hT : T = W.rawTables S)` and concludes the same
for `W.model S a b`.

The proof of Theorem C: for each pair, the twelve integer weights `eInt` are within `deltaBound p ≤ δ` of
the twelve real weights `eReal` (B1, `expFix_close`), both lie in `[0, 2^f + δ]` (`expFix_le`,
`realExp_bounds`), so the integer run (cast, `logits_cast`) and the real-exp run differ by at most
`Ebound` in every logit (B2, `logits_close`); with `hA`, `strict_max_of_margin` puts the real-exp run's
strict maximum at `ans a b`; `realExp_eq_mq` divides by `D* S^6 > 0`.

## The constants, and how `E` is assembled

`Ebound S f δ B` (`Logits.lean`), with `Me = 2^f + δ`, `MD = 3 Me`, `dDh = 3 δ`, `dD = 4 dDh MD^3`, `dc = 3 dDh MD^2`:

    dAtt f δ Bh = sum_h (dc (3 Me) Bh h + MD^3 (3 δ) Bh h)
    dPre f δ B  = dD B.CI + dAtt f δ B.TI
    Ebound      = dD B.CU + S^2 dAtt f δ B.TU + B.G dPre f δ B

With `B.TI h = Omax_h ‖Win‖`, `B.TU h = Omax_h ‖U‖`, `B.CI = S^2 |x_2| ‖Win‖ + |bin|`, `B.CU = S^4 |x_2| ‖U‖ + |bout| ‖U‖`,
`B.G = ‖Wout‖ ‖U‖` this is, term for term, `error_bound_E` of `int_transformer.py` (DESIGN.md section 5:
`E = ‖U‖ (S^2 dr + ‖Wout‖ dpre + |bout| dD)`, `dr = S^2 |x_2| dD + dA`, `dpre = ‖Win‖ dr + |bin| dD`, expanded).
`chosenBounds` uses the measured norms of `scan_best_epoch3044.txt` at `q = 8`: `Omax = [33001994, 31898447, 33144298, 33210799]`,
`‖Win‖ = 3272`, `|bin| = 520813984`, `‖Wout‖ = 8774`, `|bout| = 71585923072`, `‖U‖ = 2025`, `|x_2| = 117`;
`Ebound_chosen` checks (by `norm_num`) that the value is the design's `E = 416063585574805997938804232439435952711840399411200`.
The bounds are on the tables, not on the raw matrices, because the tables are what the kernel program reads;
a core-lane check of `|TI h j tk i| ≤ Omax_h ‖Win‖` on the table entries is a `decide`, as is any smaller
bound that the actual entries satisfy (a smaller `B` gives a smaller `Ebound`, and `hA` with the design's
`E` then still holds, so nothing has to be recomputed).

Chosen `expFix` parameters: `t = 32` (`S = 2^8`, `t = 4q`), `f = 32`, `n = 16`, `m = 5`, `R = 24`; `deltaBound chosen = 1.00697941760`
exactly (`int_transformer.py` reports its ceiling, `2`); the proved bound is `2` (`expFix_close_chosen`). `tau 16 = 17 / (16! 16) = 5.078e-14`.

## Cost (measured, `verify.out`, 4 cores shared with two other lanes, `LEAN_NUM_THREADS=1`)

| Step | Time |
| --- | --- |
| `lake build Transformer.ExpFix` (one module, Mathlib oleans cached) | 26 s (10 s in the first run) |
| `lake build Transformer.Program`, `Logits`, `Compose`, `Raw` | 10 s, 9 s, 8 s, 46 s (first run, under load: 12 s, 70 s, 83 s, not built) |
| `leanchecker` replay, one module per call | 10 s, 8 s, 8 s, 8 s, 9 s (first run, under load: 67 s, 68 s, 70 s, 11 s) |
| `lake env lean axioms_all.lean` (64 `#print axioms`) | 8 s |
| peak resident memory of `lean` on `Transformer/Raw.lean` (poll of `/proc` every 0.5 s, `rss.Raw.out`) | 2232 MB |

The whole `verify.sh` ran from `17:11:02Z` to `17:13:48Z`. The elaboration of `deltaBound_chosen` (the
exact rational `(1 + 17/334764638208000)^31` by `norm_num`) is inside `ExpFix`'s 10 s.

## What remains to make Theorem C unconditional

`real_model_adds_mod_113_chosen T hB hA` needs, for the chosen tables `T` (the literal tables of
`build_tables` on `runs/best.npz` at `q = 8`):

1. `hB : T.Bounded chosenBounds`, five universally quantified absolute-value bounds on the table entries
   (`4 x 3 x 114 x 512` entries of `TI`, `4 x 3 x 114 x 113` of `TU`, `512` of `CI`, `113` of `CU`, `113` column sums of `G`).
   On a literal table each is a `decide`.
2. `hA`: on each of the 12,769 pairs, `intLogits chosen T 256 a b` has its logit at `(a + b) % 113` above every
   other logit by more than `2 E`. This is Theorem A (DESIGN.md section 8), the kernel check the core-Lean
   lane runs on its own packed program (`claude/transformer`, core Lean `v4.35.0-rc2`). Its program and
   `intLogits` here must be proved to compute the same integers: either (a) the core lane's definitions
   are imported into this project (a Lake path dependency is impossible across the two toolchains; copying
   the files in, as `phasegrid/mathlib` copies `Network.lean`, is possible since they use no Mathlib) and
   the equality `intLogits chosen T 256 a b = fastLogits ...` is proved once as a lemma about the two
   definitions (the packing route needs its digit-bound lemma), or (b) the 12,769 checks are re-run inside
   this project by `decide +kernel` on a program written in the kernel-friendly style (`Nat`/`Int`
   literals, `Int.add`/`Int.mul` spelled out, packed vectors), again with a lemma relating that program to
   `intLogits`. Either way `intLogits` as written here (`Finset` sums over `Fin 512`) is the specification,
   not the program the kernel should evaluate: `decide` on `Finset.sum` does not reduce usefully.
3. For the raw-model version, `hT : T = W.rawTables 256` with `W` the quantised matrices (one equality per
   table; on literals each is a kernel computation of the table, about 1,000 packed big-number steps in all
   by DESIGN.md's count, or a `decide` on the `Finset` form at a higher cost).

The `expFix` of this project must be the one the core lane evaluates. It is defined above in full; the
core lane either copies the definition verbatim (recommended: `horner`, `coeff`, `coeffs`, `bigF`, `expFix`
use nothing beyond core Lean, `Nat.factorial` is Mathlib's but is a one-line definition) or proves its own
equal to it on the inputs that occur. The 16 coefficients and `bigF` at the chosen parameters are printed
in `eval_check.out`, so a core-lane definition with literal coefficients can be matched by `decide` on the list.

## What was NOT done

- Theorem A is not proved and not re-checked here; no table and no weight of the trained model is in this
  project. Theorem C is conditional on `hA`, `hB` (and `hT` for the raw model), exactly as stated above.
- The link between `intLogits` and the core lane's packed program is not written; neither is the balanced-digit
  unpacking lemma that the packed route needs for signed entries (DESIGN.md section 9, item 2).
- `Ebound` is the design's uniform bound; it was not tightened (the bounds are on the maxima over all tokens and
  positions, and the four denominators are each bounded by `3 Me`).
- The clamp condition and the Taylor remainder use Mathlib's `Real.exp_one_gt_d9` and `Real.exp_bound` as given;
  no sharper exponential bounds were sought, since `deltaBound chosen = 1.007` leaves nothing to gain below `2`.
- `expFix` is proved close to `2^f exp(x/2^t)` only for `x ≤ 0`, the only inputs the program produces
  (`shifted_nonpos`); nothing is claimed for `x > 0`.
- The agreement of the Lean `expFix` with the Python `expfix` is measured on 12 inputs (`eval_check.out`), not
  proved; the agreement of `rawTables` with `build_tables` is by reading the two definitions, not by running them.
- No second independent checker beyond `leanchecker`; the toolchain binary was not compared with the official release.
- The core-Lean lane's branch (`claude/transformer`) was read for `DESIGN.md` and `int_transformer.py` only; nothing
  from it is imported, copied or modified, and nothing outside `transformer/mathlib/` changed on this branch.

## Run

    cd transformer/mathlib && lake exe cache get      # or hard-link .lake/packages from a built Mathlib v4.35.0
    LEAN_LOCK=/path/to/lean.lock ./verify.sh > verify.out 2>&1      # about 3 minutes with the oleans in place
    lake env lean eval_check.lean > eval_check.out && python3 -I check_expfix.py ../int_transformer.py > check_expfix.out

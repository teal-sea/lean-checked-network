# A one-layer transformer on addition mod 113, evaluated exactly by Lean's kernel: the design

Written 2026-10-16. This directory holds the first half of a chain: a trained one-layer transformer
(Nanda et al. 2023's model), its weights frozen to integers, and an integer program that evaluates
it with no floating point and no division, so that Lean's kernel can run it on all 12,769 pairs.
The one step a transformer cannot do in integers, the softmax's exponential, is replaced by an
integer-valued function `expFix` with a proved error bound, and a second theorem bounds what that
error can do to the logits. The Lean proofs are the next lane's work; this file states what they
prove and gives the Python reference they mirror (`int_transformer.py`). Status words follow the
house rule: **proved** (a theorem in Lean, kernel-accepted), **derived** (a pencil argument, checked
numerically here, not yet in Lean), **measured** (a Python computation), **open**.

The precedent is Gross, Kwa and Agrawal (2023), who brute-forced a theorem in Coq about a trained
Max-of-2 transformer in floating point with a tolerance. The difference aimed at here: the model
checked is an exact integer object, its evaluation in the kernel is exact, and the only
approximation (the exponential) is bounded by a theorem rather than a tolerance.

Nothing in this directory touches `lean/`, `phasegrid/` or any other directory of the repository.

## 1. The model and its training (measured)

`train.py` (PyTorch 2.14.1 CPU, `torch.set_num_threads(2)`, numpy 2.5.3, Python 3.13). Vocabulary
114: tokens 0..112 and `=` (token 113). Input `[a, b, =]`. Learned token embedding (114 x 128) and
position embedding (3 x 128); one attention layer with 4 heads of 32 (W_Q, W_K, W_V of shape
128 x 32 per head, W_O 32 x 128 per head, no biases, scores divided by sqrt(32), causal mask);
one MLP 128 -> 512 -> 128 with ReLU and biases; residual connections; no LayerNorm; unembedding
128 x 113 at the last position, no bias. Only the last position's query is computed, since with a
causal mask nothing downstream reads positions 0 and 1. AdamW, lr 1e-3, weight decay 1.0, betas
(0.9, 0.98), full batch on a seeded random half of the 12,769 pairs (6,384 train, 6,385 held out,
seed 0).

Stop rule, as implemented: train and held-out accuracy both 1.0 for 300 consecutive epochs, then a
margin phase of 2,000 epochs that adds to the cross-entropy a hinge term
`mean(relu(target - (right logit - best wrong logit)))` over the TRAIN pairs with weight 1.0, target
the median train gap at the moment the phase starts (written to the log), same weight decay. Hard
budget 3 hours wall, fallback to all pairs at 2 hours if the stop rule had not fired. Checkpoints
every 500 epochs (`runs/ckpt_*.pt` and `.npz`, not in git), `runs/best.pt` (the checkpoint with the
largest smallest-margin that is right on every pair), `runs/final.pt`. Log: `runs/train.log`, one
line per 100 epochs: epoch, train loss, train accuracy, held-out accuracy, smallest margin over all
12,769 pairs, phase.

What happened (`runs/train.log`): launched 2026-10-16T15:53:07Z (PID 1088, `python3 transformer/train.py --frac 0.5
--seed 0 --budget-hours 3 --fallback-hours 2 --runs transformer/runs`, detached with `nohup setsid`).
Train accuracy 1.0 from the epoch-200 line on (train loss 0.0143 at epoch 200, 1e-6 at epoch 1000);
held-out accuracy 0.5062 at epoch 200, 0.8818 at 700, 0.9966 at 900, 1.0000 at the epoch-1000 line;
the smallest margin over all 12,769 pairs turned positive between epochs 900 and 1000 (-2.92 at
900, 0.50 at 1000, 4.82 at 1200). The stop rule fired at epoch 1283 (both accuracies 1.0 for 300
epochs, so from epoch 984), hinge target 16.2248 (the median train gap). Margin phase epochs 1284 to
3283; the smallest margin rose from 4.8 to 13.62 at the end, with the best value 14.8414 at epoch
3044 (`runs/best.pt`, `runs/best.npz`: the chosen weights). Stop at epoch 3283, 1,108 s wall, no
fallback: the held-out set stayed held out throughout, so the chosen weights were fitted on 6,384
pairs and are right on all 12,769 (float64 and, section 7, in the integer program).

Smoke tests before the launch: `smoke_test.log` (20 epochs; the margin-phase path forced with
`--stable-epochs 0`; the budget stop forced with `--budget-hours 0.0005`; 30 epochs take 7.66 s
including startup, about 0.3 s per epoch).

## 2. Quantisation (measured)

`quantise(W, q)` in `int_transformer.py`. One scale S = 2^q for every matrix:

    E^ = round(S E)   P^ = round(S P)   WQ^ = round(S WQ / sqrt(32))   WK^, WV^, WO^ = round(S .)
    Win^ = round(S Win)   bin^ = round(S^4 bin)   Wout^ = round(S Wout)   bout^ = round(S^5 bout)   U^ = round(S U)

The 1/sqrt(32) of the attention score is folded into WQ^, so the integer score is an exact integer
at scale S^4 and the softmax's unit is t = 4q. The biases sit at S^4 and S^5 because that is the
scale the residual stream has reached when they are added (section 3). Rounding is half up
(`floor(x + 1/2)`, which is Lean's `round`).

**The quantised model M_q** is the ordinary real-valued transformer whose weights are these
integers divided by their scales (`dequantise`), with score q . k (no further 1/sqrt(32)) and a
real softmax. It is a different model from the trained float model; it is the model the final
theorem is about. Its agreement with the trained model is measured, not proved, and is reported in
the table of section 7 (`floatMq_wrong`, `trained_wrong`, both 0 at every q tried).

## 3. The integer program (derived, checked in numpy)

For a pair (a, b), with x_j = E^[tok_j] + P^[j] (tok = a, b, = at positions 0, 1, 2) and S = 2^q:

    per head h:  qh = WQ^h x_2          s_j = qh . (WK^h x_j)        (exact integers, scale S^4)
                 e_j = expFix(s_j - max_j s_j)                        (approximates 2^f exp((s_j - s_max) / 2^t))
                 D^h = e_0 + e_1 + e_2
                 w^h = WO^h (sum_j e_j WV^h x_j)                      (128; = D^h S^3 times head h's output when expFix is exact)
    D = D^1 D^2 D^3 D^4          c^h = prod_{h' != h} D^h'            (so c^h D^h = D, no division)
    A = sum_h c^h w^h                                                  (= D S^3 times the attention output of M_q)
    r = D S^2 x_2 + A                                                  (= D S^3 times the residual stream)
    pre = Win^^T r + D bin^            m = relu(pre)                   (= D S^4 times the MLP hidden layer)
    o = Wout^^T m + D bout^                                            (= D S^5 times the MLP output)
    fin = S^2 r + o                                                    (= D S^5 times the final residual)
    L = U^^T fin                                                       (= D S^6 times the logits of M_q)
    answer = argmax L, first index on a tie (as Network.lean's argmax).

**Why there is no division.** The softmax weight of position j in head h is e_j / D^h. ReLU is
positively homogeneous and everything else is linear, so multiplying the residual stream by the
positive number D = D^1 D^2 D^3 D^4 commutes with the whole tail of the network provided every
additive term (the residual x_2, the two biases) is multiplied by D too. The four heads have four
different denominators; the product D is the common one, and head h's contribution carries the
other three (c^h). The argmax is unchanged by the positive factor D S^6.

**Identity (measured).** When expFix is replaced by the exact real 2^f exp, L = D S^6 . logits(M_q)
exactly (each line above is labelled with its scale; the chain is linear except for the ReLU, which
commutes with a positive scalar). With the real expFix, `int_transformer.py` compares L / (D S^6)
against a float64 forward pass of M_q on all 12,769 pairs: largest difference 5.36e-08 at the chosen configuration
(column `max_dev_vs_floatMq` of the table in section 7), which is the exp approximation plus float
rounding. The program is written twice, from the raw matrices (`int_logits_raw`) and through
precomputed tables (`int_logits_tables`, section 6), and the two are asserted equal on 64 random
pairs per configuration.

## 4. expFix and Theorem B1: the certified exponential

Parameters: t (the score unit, t = 4q), f (the output scale), n (number of Taylor terms), m (range
reduction), R (clamp). For an integer x <= 0:

    if x < -R 2^t:  expFix x = 0
    else:   N = sum_{i<n} x^i (n-1)!/i! 2^((t+m)(n-1-i))      (an integer; Horner)
            F = (n-1)! 2^((t+m)(n-1))                           (a constant)
            expFix x = floor( 2^f N^(2^m) / F^(2^m) )

so N / F = sum_{i<n} y^i / i! with y = x / 2^(t+m), exactly, and (N/F)^(2^m) approximates
exp(y)^(2^m) = exp(x / 2^t). There is one floor, at the end; the power 2^m is even, so N^(2^m) >= 0
and the division is on natural numbers. expFix 0 = 2^f exactly (N = F), so every D^h is at least 2^f.

**Theorem B1 (to prove on Mathlib; derived here).** With tau = (n+1) / (n! n), R <= 2^m and
2^f exp(-R) <= 1:

    for every integer x <= 0,   | expFix x - 2^f exp(x / 2^t) | <= delta,
    delta = 2^f 2^m tau (1 + tau)^(2^m - 1) + 1.

Proof sketch. In range, |y| = |x| / 2^(t+m) <= R / 2^m <= 1, so Mathlib's `Real.exp_bound`
(`|exp y - sum_{i<n} y^i/i!| <= |y|^n (n+1)/(n! n)` for `|y| <= 1`, `0 < n`) gives |T - exp y| <= tau
for T = N/F; also |T| <= 1 + tau and 0 < exp y <= 1. Then
|T^N' - (exp y)^N'| = |T - exp y| |sum_k T^k (exp y)^(N'-1-k)| <= tau N' (1 + tau)^(N'-1) with N' = 2^m,
and (exp y)^N' = exp(x / 2^t). The floor moves the value by less than 1. Below the range, the
output is 0 and 0 < 2^f exp(x/2^t) < 2^f exp(-R) <= 1 <= delta; `Real.exp_one_gt_d9`
(exp 1 > 2.7182818283) makes 2^f exp(-R) <= 1 a rational inequality. `delta_bound` in
`int_transformer.py` evaluates the bound in exact rationals and returns its ceiling; with R chosen
as ceil(f ln 2) + 1 the clamp condition is checked there too.

Chosen values and their delta: section 7.

## 5. Theorem B2: from delta to a bound E on every logit

Let L~ be the program's logits (with expFix) and L* the same program with the real values
e*_j = 2^f exp((s_j - s_max)/2^t) in place of e_j. Then L* = D* S^6 logits(M_q) with D* > 0
(section 3), so argmax L* is M_q's answer. The claim is a constant E, computed once from the integer
weights, with |L~_c - L*_c| <= E for every pair and every c. Then

    margin(L~) := L~_right - max_{c != right} L~_c  >  2E   implies   argmax L* = argmax L~,

because L*_right >= L~_right - E > L~_c + E >= L*_c for every wrong c.

Derivation (every step a triangle inequality on a sum or a product; written exactly as
`error_bound_E` computes it; |.| is the entrywise maximum, ||W|| the largest absolute column sum,
i.e. the operator norm from |.|_inf to |.|_inf for v -> W^T v):

    Me  = 2^f + delta                      bounds every e_j and e*_j (e* <= 2^f, |e - e*| <= delta)
    MD  = 3 Me                             bounds every D^h, D*^h
    dDh = 3 delta                          |D^h - D*^h|
    dD  = 4 dDh MD^3                       |D - D*|   (telescoping over the four factors)
    dc  = 3 dDh MD^2                       |c^h - c*^h|   (three factors)
    Omax^h = max over positions j and tokens of |WO^h WV^h x_j|      (an exact integer from the tables)
    |w^h| <= 3 Me Omax^h,   |w^h - w*^h| <= 3 delta Omax^h
    dA  = sum_h ( dc . 3 Me Omax^h + MD^3 . 3 delta Omax^h )       |A - A*|   (c w - c* w* = (c - c*) w + c* (w - w*))
    dr  = S^2 |x_2| dD + dA
    dpre = ||Win^|| dr + |bin^| dD           ReLU is 1-Lipschitz, so |m - m*| <= dpre
    do  = ||Wout^|| dpre + |bout^| dD
    dfin = S^2 dr + do
    E   = ||U^|| dfin

**Theorem B2 (to prove on Mathlib; derived here).** For integer weights with these norms and any
two sets of twelve numbers e^h_j, e*^h_j with 0 <= e, e* <= Me and |e - e*| <= delta, the two runs
of the program differ by at most E in every logit.
In Lean this is a statement about the program as a function of the twelve numbers e^h_j, with the
real run obtained by substituting real numbers; the proof is the chain of inequalities above, each
an `abs_sub_le`/`abs_mul`/`Finset.abs_sum_le_sum_abs` step on the definitions, plus
`|relu a - relu b| <= |a - b|`.

How much room there is: E in real units of M_q is E / (D S^6) <= E / (2^(4f) S^6) since D >= 2^(4f)
(column `2E_floor_real` of the table); the leading term of E scales like
delta . 2^(3f) . (weight norms), so E / 2^(4f) scales like delta / 2^f: every extra bit of f
halves the floor, and the Taylor degree n only needs to keep delta at a few units.

## 6. What the kernel runs per pair, and the cost (derived)

The scores s_j, and everything linear that follows a token, depend only on (token, position), so
they are tables (`build_tables`), computed in Python and to be verified once by `decide` in Lean
against the raw matrices (one theorem per table, kernel cost about 1,000 packed big-number steps in
all; the identity between the raw and the table program is linear algebra, the same for every pair,
and is proved once, not per pair):

    sc[h][j][tok]    = (WQ^h x_2) . (WK^h x_j(tok))              integer scores      (4 x (113 + 113 + 1))
    TI[h][j][tok]    = Win^^T (WO^h WV^h x_j(tok))                512-vectors         (same count)
    TU[h][j][tok]    = U^^T (WO^h WV^h x_j(tok))                  113-vectors
    CI = S^2 Win^^T x_2 + bin^ (512)     CU = S^4 U^^T x_2 + U^^T bout^ (113)     G = U^^T Wout^^T (113 x 512)

and the per-pair program is

    e^h_j = expFix(sc[h][j][tok_j] - max_j sc[h][j][tok_j]),  D^h, c^h, D as in section 3
    pre = D CI + sum_h c^h sum_j e^h_j TI[h][j][tok_j]          (512)
    m   = relu(pre)
    L   = D CU + S^2 sum_h c^h sum_j e^h_j TU[h][j][tok_j] + G m  (113)
    answer = argmax L.

With the repository's packing trick (`lean/LeanCheckedNetwork/Fast.lean`: a vector of digits as
one big natural number in base B, so a scalar times a vector is one multiplication), the 512- and
113-vectors are single numbers and the per-pair count is

| step | big-integer operations |
| --- | --- |
| 12 expFix: Horner n mult-adds, the 2^m-th power (m squarings), shift, divide, compare | 12 (n + m + 3) |
| D^h (8 adds), c^h (8 mults), D (1) | 17 |
| pre: 12 scalar-times-packed-vector, 4 for c^h, 1 for D CI | 17 |
| unpack 512 digits (div, mod), ReLU on each | 1,536 |
| L: 512 packed mult-adds (G's columns times m_i), 12 + 4 + 1 + 1 for the rest | 530 |
| unpack 113 digits, argmax | 339 |
| total (n = 16, m = 5) | 2,727, of which 852 are multiply-adds on numbers of a few hundred to a few thousand bits |

The existing route (`Fast.lean`) is about 470 kernel steps per input (128 packed mult-adds, 113
unpacks, the argmax) and the trained 128-neuron network checked in about 13 minutes on 4 cores
(README). At about 6 times the steps, and with wider numbers (logits of about 190 bits times 113
digits; the m_i of about 160 bits; the expFix powers of about 20,000 bits), the estimate is 1 to 2
hours on 4 cores for all 12,769 pairs, plus the same again for the `leanchecker` replay. The
digits must stay below B: with signed digits (r, pre and L have both signs) the packing needs a
balanced base-B digit extraction, or a shift of every digit by a known constant as `shiftW` does;
B around 2^256 covers the measured sizes with room (the lane that writes the Lean picks it and
proves the digit bound once from the norms, or checks it per pair as `fastOk` does).

## 7. Measurements: (q, t, n, m), delta, E, margins (measured)

`int_transformer.py --scan` on the checkpoints; every row is an exact evaluation of all 12,769 pairs
(the integer program, Python integers, no float in the decision), with the float64 forward of M_q
and of the trained model alongside. `margin/(2E)` is the smallest integer margin over all pairs
divided by 2E; the theorem needs it above 1. `2E_floor_real` is 2E / (2^(4f) S^6), the most the
exp approximation can cost in M_q's own logit units; `min_margin_real` is the smallest
margin / (D S^6) over the pairs, i.e. M_q's own smallest logit gap.

Checkpoint `runs/best.npz` (epoch 3044), `scan_best_epoch3044.txt`; every row 12,769 pairs, 68 to 76 s
each in Python:

| q | t | f | n | m | R | delta | E (bits) | smallest margin (bits) | margin/(2E) | wrong | ties | pairs with margin <= 2E | min_margin_real | 2E_floor_real | max_dev_vs_floatMq | M_q wrong (float) | trained wrong (float) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 6 | 24 | 32 | 16 | 5 | 24 | 2 | 157 | 169 | 2,821 | 0 | 0 | 0 | 11.6912 | 0.00873 | 5.3e-08 | 0 | 0 |
| 8 | 32 | 32 | 16 | 5 | 24 | 2 | 169 | 181 | 3,259 | 0 | 0 | 0 | 14.6555 | 0.00869 | 5.36e-08 | 0 | 0 |
| 10 | 40 | 32 | 16 | 5 | 24 | 2 | 181 | 193 | 3,343 | 0 | 0 | 0 | 14.7955 | 0.0087 | 5.14e-08 | 0 | 0 |
| 12 | 48 | 32 | 16 | 5 | 24 | 2 | 193 | 205 | 3,346 | 0 | 0 | 0 | 14.8293 | 0.0087 | 5.03e-08 | 0 | 0 |
| 8 | 32 | 24 | 12 | 5 | 18 | 3 | 145 | 149 | 8.488 | 0 | 0 | 0 | 14.6555 | 3.34 | 1.32e-05 | 0 | 0 |
| 8 | 32 | 28 | 14 | 5 | 21 | 2 | 157 | 165 | 203.7 | 0 | 0 | 0 | 14.6555 | 0.139 | 7.79e-07 | 0 | 0 |
| 8 | 32 | 40 | 18 | 5 | 29 | 2 | 193 | 213 | 834,400 | 0 | 0 | 0 | 14.6555 | 3.39e-05 | 1.92e-10 | 0 | 0 |

The trained float model's smallest margin is 14.8414 (epoch 3044); M_q at q = 8 keeps 14.6555 of it,
at q = 6 11.6912. The exp approximation's possible cost (2E_floor_real) falls by about 16 for every
4 bits of f, as section 5 predicts (delta stays at 2 or 3), and is independent of q. The same
program on `runs/final.npz` (epoch 3283, `scan_final_epoch3283.txt`) at (8, 32, 32, 16, 5): margin/(2E)
3,046, smallest margin 13.6991, 0 wrong. An earlier checkpoint (epoch 1293, before most of the margin
phase, `scan_best_epoch1293.txt`) gave margin/(2E) 830 to 863 at q = 6, 8, 10: the margin phase
roughly quadrupled the room.

At the chosen configuration (q = 8): E = 416063585574805997938804232439435952711840399411200 (169 bits);
the smallest integer margin is 2712072545744072581180354764646724130914805759237991380 (181 bits) at
the pair (96, 73); the largest logit has 186 bits; the integer norms are |x_2| = 117,
Omax = [33001994, 31898447, 33144298, 33210799], ||Win^|| = 3272, |bin^| = 520813984, ||Wout^|| = 8774,
|bout^| = 71585923072, ||U^|| = 2025; the raw and table programs agreed on the 64 random pairs
checked in every row.

Random-weight prototype (`--random 0`, 2 rows): the raw and table programs agree, L / (D S^6)
matches the float forward of M_q to 5.5e-11, 225 of 226 pairs wrong, as a random model should be.

Chosen configuration: **q = 8, t = 32, f = 32, n = 16, m = 5, R = 24, delta = 2**, on `runs/best.npz` (epoch 3044).
Reasons: q = 8 keeps the trained margin (14.66 of 14.84) where q = 6 loses a fifth of it, and
q = 10 or 12 buy nothing but 12 to 24 more bits in every number; f = 32 leaves a factor 3,259
between the smallest margin and 2E (f = 28 would leave 204, f = 24 only 8.5), with n = 16 the
smallest Taylor degree that keeps delta at 2 at this f (n = 14 gives 3); m = 5 is the least with
2^m >= R = 24. Kernel steps per pair at this choice: 2,727, of which 852 are big-number
multiply-adds (section 6).

## 8. The two theorems and how they compose

**Theorem A (core Lean or the Mathlib project, brute force, `decide +kernel` per row as
`gen_lean.py` does):** with the integer tables above and the constants (t, f, n, m, R, E) as
numerals,

    for all a < 113, b < 113:   answer a b = (a + b) % 113   and   margin a b > 2 E.

The program is Nat/Int arithmetic only (Nat.pow and Nat.div are kernel-accelerated GMP
operations, as are add, mul, mod), so it is a `decide` like the repository's `fast_<a>` theorems,
113 rows of 113 pairs. The `margin` conjunct costs one extra subtraction and comparison per pair.
Also one theorem per table (section 6) saying the table equals the raw-matrix expression.

**Theorem B (Mathlib):** B1, `|expFix x - 2^f exp(x / 2^t)| <= delta` for every integer x <= 0;
B2, `|L~_c - L*_c| <= E` for every pair and every c, for the L~ built from expFix and the L* built
from 2^f exp.

**Theorem C (Mathlib; the statement about the real-softmax model):** for every a, b < 113, the
model M_q, defined with real weights (the integer tables cast to R and divided by their scales),
real exp and a real softmax, puts its largest logit at (a + b) % 113. Proof: by A the integer run
answers (a + b) % 113 with margin > 2E; by B1 and B2 the real-exp run L* is within E of it in
every logit, so it has the same argmax; L* = D* S^6 . logits(M_q) with D* > 0 (the identity of
section 3, proved as an algebraic lemma about the program's definition), so M_q has the same argmax.

Toolchains: the repository's core Lean is v4.35.0-rc2; Mathlib work is Lean v4.35.0 + Mathlib
v4.35.0 (built at the phasegrid stage 2 location). If A is proved in the core project and B, C in the
Mathlib project, C can only cite A, not import it (as phasegrid's stage 3 tables are cited and not
imported by its stage 2). The recommendation is to prove A inside the Mathlib project too (the
`decide +kernel` runs the same there; the cost is the Mathlib import per row file, about 1 GB
resident), so that C is one theorem and `#print axioms` on it covers the whole chain.

**What is exact and what is approximate.**

| object | status |
| --- | --- |
| the integer weights and tables | exact; the model M_q is defined by them |
| the per-pair integer program | exact; evaluated by the kernel |
| expFix | an approximation to 2^f exp, with a proved absolute error delta (B1) |
| the softmax denominators | carried exactly, never divided |
| the logits of M_q | real numbers; never computed; their argmax is pinned by A + B |
| the trained float model | measured only: it agrees with M_q on all 12,769 pairs (section 7), and no theorem says so |
| the held-out story | measured: M_q and the trained model were trained on 6,384 pairs and are right on the other 6,385 |

## 9. Risks

1. **Theorem B2's constant is loose by design** (uniform bounds over all pairs, products of the
   four denominators bounded by 3 Me each). The measured room (margin/(2E) in section 7) says how
   much looseness is affordable; if a future checkpoint has a smaller margin, raise f (each bit
   halves the floor) at the cost of wider numbers, not of more steps.
2. **Signed digits in the packed representation.** `Fast.lean` packs non-negative digits; here r,
   pre and L carry both signs. Either a balanced-digit unpack (digit d in (-B/2, B/2), recovered
   from N mod B) with its own lemma, or shift every entry by a known constant as `shiftW` does.
   Both are standard; neither is written yet.
3. **The 2^m-th power inside expFix** produces numbers of about 20,000 bits (N has about 600 bits
   at t + m = 37, n = 16). Twelve such powers and divisions per pair are cheap for GMP (the kernel's
   Nat.pow and Nat.div), but if the kernel's Nat.pow path is not the GMP one for some reason, use
   m repeated squarings of the one-floor-per-squaring variant (the error bound then gains a 2^m
   additive term, derived in the same way).
4. **`decide` on Int.** The program is naturally on Int (the scores and the pre-activations are
   signed). The repository's route writes Int literals as constructors and uses `Int.add`/`Int.mul`
   spelled out so the kernel does not unfold notation; the same discipline applies, and the expFix
   power should be computed on Nat after `Int.toNat` of N^2 or of |N| (N > 0 in range, which B1's
   proof shows but the kernel need not know: define it on the natural number N.natAbs, whose even
   power equals N's).
5. **Memory.** One row file with the Mathlib import, 113 `decide`s each running the program, should
   stay at about 1 to 2 GB resident like the existing row files, but the first row must be measured
   before 113 are launched; one module per `lake build`, under the shared lock.
6. **The quantised model is not the trained model.** Theorem C is about M_q. The gap between them
   is a measurement (0 disagreements at every q tried); anyone who wants a theorem about the float
   model needs a different chain.
7. **Training reproducibility.** Full-batch AdamW on CPU with 2 threads is deterministic for a given
   torch build; a different build may give a different checkpoint, so `runs/best.npz` and
   `runs/final.npz` are the objects, not the training command.

## 10. What was NOT done

- No Lean was written in this lane; Theorems A, B1, B2, C are stated, derived and checked
  numerically, not proved.
- E was not tightened per pair (a per-pair E computed by the program itself would cut the
  looseness but adds kernel steps and a lemma); not needed at the measured room.
- The trained float model's agreement with M_q is measured on all pairs, not proved; no
  theorem about the float model is claimed or planned.
- No search over seeds or train fractions beyond the one run (seed 0, 50 percent).
- The kernel time is an estimate from step counts and the repository's measured rate, not a
  measurement.

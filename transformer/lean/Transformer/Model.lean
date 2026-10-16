/-!
# The quantised one-layer transformer, as an integer program

The model of DESIGN.md section 6: a one-layer transformer (4 heads of 32, MLP 512 with ReLU, no
LayerNorm) on the input `[a, b, =]`, with every weight an integer at scale `S = 2^q`, evaluated
with no division. Everything that depends only on one token and its position is a table (`Tab`);
the per-pair program looks the tables up and combines them.

For a pair `(a, b)` and head `h`, the three attention scores are `sc0 h a`, `sc1 h b`, `sc2 h`;
`e_j = expFix (s_j - max s)` stands in for `2^f exp((s_j - max s) / 2^t)`; `D^h = e_0 + e_1 + e_2`
is head `h`'s softmax denominator and `D = D^0 D^1 D^2 D^3` the common one; head `h`'s
contribution carries the product `c^h` of the other three, so that `c^h D^h = D` and no division
is needed:

    pre = D CI + sum_h c^h (e_0 TI0 h a + e_1 TI1 h b + e_2 TI2 h)        (512 entries)
    m   = relu pre                                                        (as natural numbers)
    L   = D CU + S^2 sum_h c^h (e_0 TU0 h a + e_1 TU1 h b + e_2 TU2 h) + G^T m   (113 logits)

`L` is `D S^6` times the logits of the real-softmax model M_q when `expFix` is exact. The answer is
the index of the largest logit, the first on a tie; the margin is the right logit minus the best
wrong one.

Arithmetic on integers is written with `Int.add`, `Int.mul`, `Int.sub`, `Int.ofNat`, which are
`+`, `*`, `-` and the cast; spelling them out keeps the kernel from unfolding notation.
-/

namespace Transformer

/-- The constants of `expFix`: `f2 = 2^f`, `lo = R 2^t`, `pw = 2^m`, `cs` the Horner coefficients
`c_i = (n-1)!/i! 2^((t+m)(n-1-i))` with `c_0` first, `Fpow = ((n-1)! 2^((t+m)(n-1)))^(2^m)`;
and `S2 = S^2`. -/
structure Cfg where
  S2 : Nat
  f2 : Nat
  lo : Nat
  pw : Nat
  cs : List Nat
  Fpow : Nat

/-- The tables. `sc0 h`, `sc1 h` : scores over the token at positions 0 and 1; `sc2 h` : the score
of `=` at position 2. `TI0 h tok`, `TI1 h tok`, `TI2 h` : 512-vectors; `TU0 h tok`, `TU1 h tok`,
`TU2 h` : 113-vectors; `CI` (512), `CU` (113), `G` (512 rows of 113). -/
structure Tab where
  sc0 : List (List Int)
  sc1 : List (List Int)
  sc2 : List Int
  TI0 : List (List (List Int))
  TI1 : List (List (List Int))
  TI2 : List (List Int)
  TU0 : List (List (List Int))
  TU1 : List (List (List Int))
  TU2 : List (List Int)
  CI : List Int
  CU : List Int
  G : List (List Int)

/-- Entry `n` of a list, `d` if out of range. -/
def nth {α : Type} (d : α) : List α → Nat → α
  | x :: _, 0 => x
  | _ :: xs, n + 1 => nth d xs n
  | [], _ => d

/-- `horner [c_0, ..., c_{n-1}] x = c_0 + x (c_1 + x (... ))  = sum_i c_i x^i`. -/
def horner : List Nat → Int → Int
  | [], _ => 0
  | c :: cs, x => Int.add (Int.ofNat c) (Int.mul x (horner cs x))

/-- The integer stand-in for `2^f exp(x / 2^t)` on `x ≤ 0` (DESIGN.md section 4): `0` below the
clamp, else `floor(2^f N^(2^m) / F^(2^m))` with `N = horner cs x`; the even power is taken on
`|N|`, which equals `N^(2^m)`. -/
def expFix (K : Cfg) (x : Int) : Nat :=
  if x < Int.neg (Int.ofNat K.lo) then 0
  else (K.f2 * (horner K.cs x).natAbs ^ K.pw) / K.Fpow

def maxI (a b : Int) : Int := if a < b then b else a

/-- The three exp weights of head `h` for the pair `(a, b)`. -/
def headE (K : Cfg) (T : Tab) (a b h : Nat) : Nat × Nat × Nat :=
  let s0 := nth 0 (nth [] T.sc0 h) a
  let s1 := nth 0 (nth [] T.sc1 h) b
  let s2 := nth 0 T.sc2 h
  let smax := maxI s0 (maxI s1 s2)
  (expFix K (Int.sub s0 smax), expFix K (Int.sub s1 smax), expFix K (Int.sub s2 smax))

/-- Head `h`'s denominator `D^h = e_0 + e_1 + e_2`. -/
def den (e : Nat × Nat × Nat) : Nat := e.1 + e.2.1 + e.2.2

/-- `(D, (c^0, c^1, c^2, c^3))`: the common denominator and the four cofactors. -/
def dens (E0 E1 E2 E3 : Nat × Nat × Nat) : Nat × (Nat × Nat × Nat × Nat) :=
  let D0 := den E0
  let D1 := den E1
  let D2 := den E2
  let D3 := den E3
  (D0 * D1 * D2 * D3, (D1 * D2 * D3, D0 * D2 * D3, D0 * D1 * D3, D0 * D1 * D2))

/-- A natural number times an integer vector. -/
def smulN (c : Nat) (v : List Int) : List Int := v.map (fun x => Int.mul (Int.ofNat c) x)

/-- Entry-by-entry sum; the longer list's tail is kept (every vector here has the same length). -/
def vadd : List Int → List Int → List Int
  | x :: xs, y :: ys => Int.add x y :: vadd xs ys
  | [], ys => ys
  | xs, [] => xs

/-- `e_0 v_0 + e_1 v_1 + e_2 v_2`: one head's weighted sum of its three value vectors. -/
def headVec (e : Nat × Nat × Nat) (v0 v1 v2 : List Int) : List Int :=
  vadd (smulN e.1 v0) (vadd (smulN e.2.1 v1) (smulN e.2.2 v2))

/-- `sum_i c_i row_i`: the rows of `G` weighted by the hidden layer. -/
def lincombN : List Nat → List (List Int) → List Int
  | c :: cs, r :: rs => vadd (smulN c r) (lincombN cs rs)
  | _, _ => []

/-- Head `h`'s weighted value vector from the `TI` tables (for `pre`). -/
def headI (T : Tab) (a b h : Nat) (e : Nat × Nat × Nat) : List Int :=
  headVec e (nth [] (nth [] T.TI0 h) a) (nth [] (nth [] T.TI1 h) b) (nth [] T.TI2 h)

/-- Head `h`'s weighted value vector from the `TU` tables (for the logits). -/
def headU (T : Tab) (a b h : Nat) (e : Nat × Nat × Nat) : List Int :=
  headVec e (nth [] (nth [] T.TU0 h) a) (nth [] (nth [] T.TU1 h) b) (nth [] T.TU2 h)

/-- The MLP pre-activations, times `D` (512 entries). -/
def preAct (K : Cfg) (T : Tab) (a b : Nat) : List Int :=
  let E0 := headE K T a b 0
  let E1 := headE K T a b 1
  let E2 := headE K T a b 2
  let E3 := headE K T a b 3
  let dc := dens E0 E1 E2 E3
  vadd (smulN dc.1 T.CI)
    (vadd (smulN dc.2.1 (headI T a b 0 E0))
      (vadd (smulN dc.2.2.1 (headI T a b 1 E1))
        (vadd (smulN dc.2.2.2.1 (headI T a b 2 E2)) (smulN dc.2.2.2.2 (headI T a b 3 E3)))))

/-- The 113 logits, times `D S^6`. ReLU is `Int.toNat`: `max x 0` as a natural number. -/
def logits (K : Cfg) (T : Tab) (a b : Nat) : List Int :=
  let E0 := headE K T a b 0
  let E1 := headE K T a b 1
  let E2 := headE K T a b 2
  let E3 := headE K T a b 3
  let dc := dens E0 E1 E2 E3
  let m := (preAct K T a b).map Int.toNat
  vadd (smulN dc.1 T.CU)
    (vadd (smulN K.S2
        (vadd (smulN dc.2.1 (headU T a b 0 E0))
          (vadd (smulN dc.2.2.1 (headU T a b 1 E1))
            (vadd (smulN dc.2.2.2.1 (headU T a b 2 E2)) (smulN dc.2.2.2.2 (headU T a b 3 E3))))))
      (lincombN m T.G))

/-- Index of the largest entry, scanning from index `i`; the best so far is at `bi` with value `bv`. -/
def argmaxFrom : List Int → Nat → Nat → Int → Nat
  | x :: xs, i, bi, bv => if bv < x then argmaxFrom xs (i + 1) i x else argmaxFrom xs (i + 1) bi bv
  | [], _, bi, _ => bi

/-- Index of the largest entry, the first one on a tie. -/
def argmax : List Int → Nat
  | x :: xs => argmaxFrom xs 1 0 x
  | [] => 0

/-- The largest entry at an index other than `c`, scanning from index `i` with the best so far `acc`. -/
def maxExceptFrom : List Int → Nat → Nat → Int → Int
  | x :: xs, i, c, acc => if i = c then maxExceptFrom xs (i + 1) c acc else maxExceptFrom xs (i + 1) c (maxI acc x)
  | [], _, _, acc => acc

/-- The largest entry at an index other than `c` (the list has at least two entries). -/
def maxExcept (L : List Int) (c : Nat) : Int :=
  maxExceptFrom L 0 c (nth 0 L (if c = 0 then 1 else 0))

/-- The model's answer: the index of the largest logit. -/
def answer (K : Cfg) (T : Tab) (a b : Nat) : Nat := argmax (logits K T a b)

/-- The logit of `(a + b) % 113` minus the largest other logit. -/
def margin (K : Cfg) (T : Tab) (a b : Nat) : Int :=
  let L := logits K T a b
  let c := (a + b) % 113
  Int.sub (nth 0 L c) (maxExcept L c)

end Transformer

import TransformerCore.Model

/-!
# The packed evaluator the kernel runs

The plain program of `Model.lean` costs about 80,000 big-integer operations per pair (512 entries
of `pre`, 113 logits, each a sum of 17 or 530 terms). This file computes the same answer and the
same margin with about 2,700 operations per pair, by writing each vector as the digits of one
large number in base `B = 2^208`: a scalar times a vector, and a sum of vectors, are then single
operations on large numbers. The packing `pkI` is linear, so the tables are packed as they are
(signed digits) and the per-pair combination is the same formula as `preAct` and `logits` on the
packed numbers. Before the digits are read back, a shift `K` that bounds every entry is added to
each digit (one addition of `K * ones`), which makes the digits natural numbers; ReLU is then the
truncated subtraction `d - K` on each digit, and the argmax and the margin are unchanged by the
shift of the logits. `fastCheck` also checks that the digits stay below `B`.

`Equiv.lean` proves that `fastCheck` passing implies the statement about the plain program.
-/

namespace TransformerCore

/-- The base of the packed representation, `2^208`. -/
def B : Nat := 411376139330301510538742295639337626245683966408394965837152256

theorem B_eq : B = 2 ^ 208 := by decide

theorem B_pos : 0 < B := by decide

/-- Digits `[d0, d1, ...]` packed as `d0 + B * (d1 + B * (...))`. -/
def pk : List Nat → Nat
  | [] => 0
  | d :: ds => d + B * pk ds

/-- The same packing on signed digits, as an integer. -/
def pkI : List Int → Int
  | [] => 0
  | d :: ds => Int.add d (Int.mul (Int.ofNat B) (pkI ds))

/-- The first `n` base-`B` digits of `N`. -/
def unpk : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, N => N % B :: unpk n (N / B)

/-- The first `n` digits of `N`, each with `K` subtracted (truncated): ReLU on shifted digits. -/
def unpkSub : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | n + 1, N, K => (N % B - K) :: unpkSub n (N / B) K

/-- `sum_i m_i * g_i` with `m_i` natural and `g_i` (packed rows) integers. -/
def dotNI : List Nat → List Int → Int
  | m :: ms, g :: gs => Int.add (Int.mul (Int.ofNat m) g) (dotNI ms gs)
  | _, _ => 0

/-- The packed vector of `n` ones. -/
def ones (n : Nat) : Nat := pk (List.replicate n 1)

/-- Index of the largest entry of a list of natural numbers, the first on a tie. -/
def argmaxFromN : List Nat → Nat → Nat → Nat → Nat
  | x :: xs, i, bi, bv => if bv < x then argmaxFromN xs (i + 1) i x else argmaxFromN xs (i + 1) bi bv
  | [], _, bi, _ => bi

def argmaxN : List Nat → Nat
  | x :: xs => argmaxFromN xs 1 0 x
  | [] => 0

def maxN (a b : Nat) : Nat := if a < b then b else a

def maxExceptFromN : List Nat → Nat → Nat → Nat → Nat
  | x :: xs, i, c, acc => if i = c then maxExceptFromN xs (i + 1) c acc else maxExceptFromN xs (i + 1) c (maxN acc x)
  | [], _, _, acc => acc

def maxExceptN (L : List Nat) (c : Nat) : Nat :=
  maxExceptFromN L 0 c (nth 0 L (if c = 0 then 1 else 0))

/-- Bounds on the absolute entries of the tables, checked once by `tablesOk`. -/
structure Bnd where
  kTI : Nat
  kCI : Nat
  kTU : Nat
  kCU : Nat
  kG : Nat

/-- A vector of length `n` with every entry in `[-k, k]`. -/
def vecOk (n k : Nat) (v : List Int) : Bool :=
  v.length == n && v.all (fun x => decide (-(Int.ofNat k) ≤ x) && decide (x ≤ Int.ofNat k))

/-- The shape and bounds of every table: 4 heads, 114 tokens, 512- and 113-vectors, entries within `bd`. -/
def tablesOk (T : Tab) (bd : Bnd) : Bool :=
  T.TI0.length == 4 && T.TI0.all (fun h => h.length == 114 && h.all (vecOk 512 bd.kTI)) &&
  T.TI1.length == 4 && T.TI1.all (fun h => h.length == 114 && h.all (vecOk 512 bd.kTI)) &&
  T.TI2.length == 4 && T.TI2.all (vecOk 512 bd.kTI) &&
  T.TU0.length == 4 && T.TU0.all (fun h => h.length == 114 && h.all (vecOk 113 bd.kTU)) &&
  T.TU1.length == 4 && T.TU1.all (fun h => h.length == 114 && h.all (vecOk 113 bd.kTU)) &&
  T.TU2.length == 4 && T.TU2.all (vecOk 113 bd.kTU) &&
  vecOk 512 bd.kCI T.CI && vecOk 113 bd.kCU T.CU && T.G.all (vecOk 113 bd.kG)

/-- `n * z` for `n : Nat`, `z : Int`. -/
def nmul (n : Nat) (z : Int) : Int := Int.mul (Int.ofNat n) z

/-- One head's packed weighted value: `e_0 pkI v0 + (e_1 pkI v1 + e_2 pkI v2)`. -/
def headPk (e : Nat × Nat × Nat) (v0 v1 v2 : List Int) : Int :=
  Int.add (nmul e.1 (pkI v0)) (Int.add (nmul e.2.1 (pkI v1)) (nmul e.2.2 (pkI v2)))

/-- The bound matching `headPk`: `e_0 k + (e_1 k + e_2 k)`. -/
def headK (e : Nat × Nat × Nat) (k : Nat) : Nat := e.1 * k + (e.2.1 * k + e.2.2 * k)

/-- The per-pair check: the digit bounds hold, the answer is `(a + b) % 113`, and the margin is
above `E2`. Computes `pre` and the logits as packed numbers. -/
def fastCheck (K : Cfg) (T : Tab) (bd : Bnd) (E2 : Nat) (a b : Nat) : Bool :=
  let E0 := headE K T a b 0
  let E1 := headE K T a b 1
  let E2' := headE K T a b 2
  let E3 := headE K T a b 3
  let dc := dens E0 E1 E2' E3
  let D := dc.1
  let c0 := dc.2.1
  let c1 := dc.2.2.1
  let c2 := dc.2.2.2.1
  let c3 := dc.2.2.2.2
  let preP : Int := Int.add (nmul D (pkI T.CI))
    (Int.add (nmul c0 (headPk E0 (nth [] (nth [] T.TI0 0) a) (nth [] (nth [] T.TI1 0) b) (nth [] T.TI2 0)))
      (Int.add (nmul c1 (headPk E1 (nth [] (nth [] T.TI0 1) a) (nth [] (nth [] T.TI1 1) b) (nth [] T.TI2 1)))
        (Int.add (nmul c2 (headPk E2' (nth [] (nth [] T.TI0 2) a) (nth [] (nth [] T.TI1 2) b) (nth [] T.TI2 2)))
          (nmul c3 (headPk E3 (nth [] (nth [] T.TI0 3) a) (nth [] (nth [] T.TI1 3) b) (nth [] T.TI2 3))))))
  let Kp : Nat := D * bd.kCI + (c0 * headK E0 bd.kTI + (c1 * headK E1 bd.kTI + (c2 * headK E2' bd.kTI + c3 * headK E3 bd.kTI)))
  let m : List Nat := unpkSub 512 (Int.toNat (Int.add preP (nmul Kp (Int.ofNat (ones 512))))) Kp
  let LP : Int := Int.add (nmul D (pkI T.CU))
    (Int.add (nmul K.S2
        (Int.add (nmul c0 (headPk E0 (nth [] (nth [] T.TU0 0) a) (nth [] (nth [] T.TU1 0) b) (nth [] T.TU2 0)))
          (Int.add (nmul c1 (headPk E1 (nth [] (nth [] T.TU0 1) a) (nth [] (nth [] T.TU1 1) b) (nth [] T.TU2 1)))
            (Int.add (nmul c2 (headPk E2' (nth [] (nth [] T.TU0 2) a) (nth [] (nth [] T.TU1 2) b) (nth [] T.TU2 2)))
              (nmul c3 (headPk E3 (nth [] (nth [] T.TU0 3) a) (nth [] (nth [] T.TU1 3) b) (nth [] T.TU2 3)))))))
      (dotNI m (T.G.map pkI)))
  let KL : Nat := D * bd.kCU + (K.S2 * (c0 * headK E0 bd.kTU + (c1 * headK E1 bd.kTU + (c2 * headK E2' bd.kTU + c3 * headK E3 bd.kTU))) + 512 * Kp * bd.kG)
  let d : List Nat := unpk 113 (Int.toNat (Int.add LP (nmul KL (Int.ofNat (ones 113)))))
  let right := (a + b) % 113
  decide (2 * Kp < B) && decide (2 * KL < B) && (argmaxN d == right) && decide (maxExceptN d right + E2 < nth 0 d right)

end TransformerCore

import LeanCheckedNetwork.Network

/-!
# The bridge between a trained network and its clock-plus-bias reduction

The reduction keeps, per neuron, one Fourier wave of each weight column (chosen in Python, the one
measured step of the chain) and appends a few constant neurons whose read-out columns carry the
bias that cancels the clock's per-class baseline. This file states, in exact integer arithmetic
the kernel decides, how the two tables relate: the first `H` columns of the reduction are within
a stated fraction of the trained table's energy, and the extra columns are constants.
-/

namespace LeanCheckedNetwork

/-- Sum of squares of a row. -/
def sumSqRow : List Int → Int
  | x :: xs => Int.add (Int.mul x x) (sumSqRow xs)
  | [] => 0

/-- Sum of squares of a table. -/
def sumSq : List (List Int) → Int
  | r :: rs => Int.add (sumSqRow r) (sumSq rs)
  | [] => 0

/-- Entry-by-entry difference of two rows (truncated to the shorter). -/
def diffRow : List Int → List Int → List Int
  | x :: xs, y :: ys => Int.sub x y :: diffRow xs ys
  | _, _ => []

/-- Row-by-row difference of two tables (truncated to the shorter). -/
def diffTable : List (List Int) → List (List Int) → List (List Int)
  | r :: rs, s :: ss => diffRow r s :: diffTable rs ss
  | _, _ => []

/-- The first `H` entries of every row. -/
def takeCols (H : Nat) (T : List (List Int)) : List (List Int) := T.map (·.take H)

/-- `T` has `n` rows of length `H`, `P` has `n` rows of length `H + m`. -/
def shapeOk (T P : List (List Int)) (n H m : Nat) : Bool :=
  T.length == n && P.length == n && T.all (·.length == H) && P.all (·.length == H + m)

/-- `den * sum (T - P_H)^2 ≤ num * sum T^2`: the first `H` columns of `P` are within `num/den`
of `T`'s energy. -/
def energyWithin (T P : List (List Int)) (H num den : Nat) : Bool :=
  decide (Int.mul (Int.ofNat den) (sumSq (diffTable T (takeCols H P))) ≤ Int.mul (Int.ofNat num) (sumSq T))

/-- Every entry past column `H` equals `v`. -/
def extraColsConst (T : List (List Int)) (H : Nat) (v : Int) : Bool :=
  T.all (fun r => (r.drop H).all (· == v))

end LeanCheckedNetwork

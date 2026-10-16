/-!
# The network

A two-layer network that adds modulo p. For an input pair `(a, b)` it takes row `a` of `E1`
and row `b` of `E2`, adds them entry by entry, squares each entry (one entry per neuron),
and gives every candidate answer `c` the score `sum over neurons of W2[c] * hidden`. The answer
is the `c` with the highest score, the first one on a tie.

Arithmetic is written with `Int.add` and `Int.mul`, which are `+` and `*` on integers; spelling
them out keeps Lean's kernel from unfolding the notation on every step.
-/

namespace LeanCheckedNetwork

/-- Row `n` of a table (the empty row if `n` is out of range). -/
def nth : List (List Int) → Nat → List Int
  | r :: _, 0 => r
  | _ :: rs, n + 1 => nth rs n
  | [], _ => []

/-- The hidden layer: `(x + y)^2` entry by entry. -/
def hidden : List Int → List Int → List Int
  | x :: xs, y :: ys => Int.mul (Int.add x y) (Int.add x y) :: hidden xs ys
  | _, _ => []

/-- Sum of entry-by-entry products. -/
def dot : List Int → List Int → Int
  | x :: xs, y :: ys => Int.add (Int.mul x y) (dot xs ys)
  | _, _ => 0

/-- One score per candidate answer: `dot (row c of W2) h`. -/
def scores (h : List Int) : List (List Int) → List Int
  | w :: ws => dot w h :: scores h ws
  | [] => []

/-- Index of the largest entry, scanning from index `i`; the best so far is at `bi` with value `bv`. -/
def argmaxFrom : List Int → Nat → Nat → Int → Nat
  | x :: xs, i, bi, bv => if bv < x then argmaxFrom xs (i + 1) i x else argmaxFrom xs (i + 1) bi bv
  | [], _, bi, _ => bi

/-- Index of the largest entry, the first one on a tie. -/
def argmax : List Int → Nat
  | x :: xs => argmaxFrom xs 1 0 x
  | [] => 0

/-- The network's answer for the pair `(a, b)`, given its weight tables. -/
def answer (E1 E2 W2 : List (List Int)) (a b : Nat) : Nat :=
  argmax (scores (hidden (nth E1 a) (nth E2 b)) W2)

end LeanCheckedNetwork

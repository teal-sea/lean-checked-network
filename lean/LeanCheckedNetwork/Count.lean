import LeanCheckedNetwork.Fast

/-!
# Counting the right answers with the fast evaluator

`adds_mod_p` says a network is right on every pair. A trained network part way through training
is right on some number of pairs, and that number is what a study of training certifies, run by
run and checkpoint by checkpoint. This file gives the count the same treatment as the answer.

The count is taken row by row (`rowCount`: how many `b < p` get `(a + b) % p` right for a fixed
`a`), because one kernel evaluation per row keeps memory small, exactly as the row proofs of
`adds_mod_p` do. `rowCount_eq_fastRowCount` says the fast evaluator's row count is the network's
row count whenever the evaluator's cheap checks pass on that row. `count` is the sum of the rows.
-/

namespace LeanCheckedNetwork

/-- How many `b < p` the network answers correctly for the first input `a`, by the plain definition. -/
def rowCount (E1 E2 W2 : List (List Int)) (p a : Nat) : Nat :=
  ((List.range p).filter fun b => answer E1 E2 W2 a b == (a + b) % p).length

/-- The same row count, computed with the fast evaluator. -/
def fastRowCount (E1 E2 W2 : List (List Int)) (H p a : Nat) : Nat :=
  ((List.range p).filter fun b => fastAnswer E1 E2 W2 H a b == (a + b) % p).length

/-- The fast evaluator's checks, on every `b < p` of row `a`. -/
def rowOk (E1 E2 : List (List Int)) (H p a : Nat) : Bool :=
  (List.range p).all fun b => fastOk E1 E2 H a b

/-- How many of the `p * p` pairs the network answers correctly: the sum of the row counts. -/
def count (E1 E2 W2 : List (List Int)) (p : Nat) : Nat :=
  ((List.range p).map fun a => rowCount E1 E2 W2 p a).sum

theorem rowCount_eq_fastRowCount (E1 E2 W2 : List (List Int)) (H p a : Nat)
    (ht : tableOk W2 H = true) (hok : rowOk E1 E2 H p a = true) :
    rowCount E1 E2 W2 p a = fastRowCount E1 E2 W2 H p a := by
  unfold rowCount fastRowCount
  congr 1
  apply List.filter_congr
  intro b hb
  have h : fastOk E1 E2 H a b = true := by
    simp only [rowOk, List.all_eq_true] at hok
    exact hok b hb
  rw [answer_eq_fastAnswer E1 E2 W2 H a b ht h]

end LeanCheckedNetwork

import Mathlib
import PhaseGrid.Network

/-!
# Lemmas about the repo's network definitions

`Network.lean` is a verbatim copy of `lean/LeanCheckedNetwork/Network.lean` from the first repository.
This file connects its list-based definitions to sums and to an index-based statement of `argmax`:
`argmax` returns the index of a strict maximum, and `answer` on tables built with `List.ofFn` is the
`argmax` of the list of scores `sum over neurons of w * (e1 + e2)^2`.
-/

namespace LeanCheckedNetwork

/-- `argmaxFrom` keeps the best so far when nothing ahead beats it. -/
theorem argmaxFrom_of_le (xs : List Int) (i bi : Nat) (bv : Int) (h : ∀ x ∈ xs, x ≤ bv) :
    argmaxFrom xs i bi bv = bi := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≤ bv := h x (by simp)
    simp only [argmaxFrom, ite_eq_right (not_lt.mpr hx)]
    exact ih (i + 1) (fun y hy => h y (by simp [hy]))

/-- `argmaxFrom` finds a strict maximum ahead of it: position `j` of `xs`, which beats the best so
far, everything before it, and is not beaten by anything after it. -/
theorem argmaxFrom_of_strict (xs : List Int) (j : Nat) (hj : j < xs.length) (i bi : Nat) (bv : Int)
    (hbv : bv < xs[j])
    (hbefore : ∀ k (hk : k < xs.length), k < j → xs[k] < xs[j])
    (hafter : ∀ k (hk : k < xs.length), j < k → xs[k] ≤ xs[j]) :
    argmaxFrom xs i bi bv = i + j := by
  induction xs generalizing i bi bv j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero] at hbv hafter
      simp only [argmaxFrom, ite_eq_left hbv, Nat.add_zero]
      apply argmaxFrom_of_le
      intro y hy
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
      exact hafter (k + 1) (by simp; omega) (by omega)
    | succ j =>
      have hj' : j < xs.length := by simp at hj; omega
      simp only [List.getElem_cons_succ] at hbv
      have hx : x < xs[j] := hbefore 0 (by simp) (by omega)
      have hbefore' : ∀ k (hk : k < xs.length), k < j → xs[k] < xs[j] := fun k hk hkj =>
        hbefore (k + 1) (by simp; omega) (by omega)
      have hafter' : ∀ k (hk : k < xs.length), j < k → xs[k] ≤ xs[j] := fun k hk hkj =>
        hafter (k + 1) (by simp; omega) (by omega)
      simp only [argmaxFrom]
      split_ifs with hlt
      · rw [ih j hj' (i + 1) i x hx hbefore' hafter']; omega
      · rw [ih j hj' (i + 1) bi bv hbv hbefore' hafter']; omega

/-- `argmax` returns the index of a strict maximum. -/
theorem argmax_of_strict (l : List Int) (i : Nat) (hi : i < l.length)
    (h : ∀ j (hj : j < l.length), j ≠ i → l[j] < l[i]) : argmax l = i := by
  cases l with
  | nil => simp at hi
  | cons x xs =>
    cases i with
    | zero =>
      simp only [argmax]
      apply argmaxFrom_of_le
      intro y hy
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
      exact le_of_lt (h (k + 1) (by simp; omega) (by omega))
    | succ i =>
      simp only [argmax]
      have hi' : i < xs.length := by simp at hi; omega
      rw [argmaxFrom_of_strict xs i hi' 1 0 x (h 0 (by simp) (by omega))
        (fun k hk hki => h (k + 1) (by simp; omega) (by omega))
        (fun k hk hik => le_of_lt (h (k + 1) (by simp; omega) (by omega)))]
      omega

/-- Row `a` of a table built with `List.ofFn`. -/
theorem nth_ofFn {n : Nat} (f : Fin n → List Int) (a : Nat) (ha : a < n) :
    nth (List.ofFn f) a = f ⟨a, ha⟩ := by
  induction n generalizing a with
  | zero => omega
  | succ n ih =>
    rw [List.ofFn_succ]
    cases a with
    | zero => rfl
    | succ a =>
      simp only [nth]
      rw [ih (fun i => f i.succ) a (by omega)]
      rfl

/-- The hidden layer on two columns indexed by the same list of neurons. -/
theorem hidden_map {α : Type} (N : List α) (f g : α → Int) :
    hidden (N.map f) (N.map g) = N.map (fun n => (f n + g n) * (f n + g n)) := by
  induction N with
  | nil => rfl
  | cons n N ih => simp only [List.map_cons, hidden, ih]; rfl

/-- The dot product on two columns indexed by the same list of neurons. -/
theorem dot_map {α : Type} (N : List α) (f g : α → Int) :
    dot (N.map f) (N.map g) = (N.map fun n => f n * g n).sum := by
  induction N with
  | nil => rfl
  | cons n N ih => simp only [List.map_cons, dot, List.sum_cons, ih]; rfl

theorem scores_eq_map (h : List Int) (W : List (List Int)) :
    scores h W = W.map (fun w => dot w h) := by
  induction W with
  | nil => rfl
  | cons w ws ih => simp [scores, ih]

/-- `answer` on tables built with `List.ofFn` over a list of neurons `N`: the `argmax` of the scores
`sum over n in N of w c n * (e1 a n + e2 b n)^2`, one per candidate answer `c < p`. -/
theorem answer_ofFn {p : Nat} {α : Type} (N : List α) (e1 e2 w : Nat → α → Int) (a b : Nat)
    (ha : a < p) (hb : b < p) :
    answer (List.ofFn fun a : Fin p => N.map (e1 a)) (List.ofFn fun b : Fin p => N.map (e2 b))
        (List.ofFn fun c : Fin p => N.map (w c)) a b
      = argmax (List.ofFn fun c : Fin p =>
          (N.map fun n => w c n * ((e1 a n + e2 b n) * (e1 a n + e2 b n))).sum) := by
  unfold answer
  rw [nth_ofFn _ a ha, nth_ofFn _ b hb, hidden_map, scores_eq_map, List.map_ofFn]
  show argmax (List.ofFn fun c : Fin p =>
    dot (N.map (w c)) (N.map fun n => (e1 a n + e2 b n) * (e1 a n + e2 b n))) = _
  simp only [dot_map]

end LeanCheckedNetwork

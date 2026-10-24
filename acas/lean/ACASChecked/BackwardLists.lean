import ACASChecked.ListAlgebra
namespace CertSound
open RouteA RouteNC

@[simp] theorem scale_length (p : Int) (xs : List Int) : (scale p xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [scale, List.length_cons] using congrArg Nat.succ ih

@[simp] theorem signs_length (xs : List Int) : (signs xs).length = 2*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => change (signs xs).length+1+1 = 2*(xs.length+1); omega

@[simp] theorem signs_even (xs : List Int) (i : Nat) : (signs xs).getD (2*i) 0 = xs.getD i 0 := by
  induction xs generalizing i with
  | nil => simp [signs]
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have he : 2*(i+1) = 2*i+1+1 := by omega
      rw [he]
      change (signs xs).getD (2*i) 0 = _
      exact ih i

@[simp] theorem signs_odd (xs : List Int) (i : Nat) : (signs xs).getD (2*i+1) 0 = -(xs.getD i 0) := by
  induction xs generalizing i with
  | nil => simp [signs]
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have he : 2*(i+1)+1 = (2*i+1)+1+1 := by omega
      rw [he]
      change (signs xs).getD (2*i+1) 0 = _
      exact ih i

theorem getD_append_front {α : Type} (xs ys : List α) (j : Nat) (d : α) (hj : j < xs.length) :
    (xs++ys).getD j d = xs.getD j d := by
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_append]; omega), List.getD_eq_getElem _ _ hj]
  exact List.getElem_append_left hj

theorem getD_append_back {α : Type} (xs ys : List α) (j : Nat) (d : α) :
    (xs++ys).getD (xs.length+j) d = ys.getD j d := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    change (x :: (xs++ys)).getD (xs.length+1+j) d = _
    have he : xs.length+1+j = (xs.length+j)+1 := by omega
    rw [he, List.getD_cons_succ, ih]

theorem appendRows_ofFn {n : Nat} (a b : Fin n → List Int) :
    appendRows (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => a i ++ b i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
    change (a 0 ++ b 0) :: appendRows (List.ofFn (fun i => a i.succ))
      (List.ofFn (fun i => b i.succ)) = _
    rw [ih]

/-- Top-target columns stop at their own bias; deeper columns retain the remaining sum. -/
theorem s_front (b next residual : List Int) (j : Nat) (hj : j < 2*b.length) :
    (addV (scale (Q*Q) (signs b) ++ next) residual).getD j 0 =
      Q*Q*(signs b).getD j 0 + residual.getD j 0 := by
  rw [addV_getD, getD_append_front _ _ _ _ (by simpa using hj), scale_getD]

theorem s_back (b next residual : List Int) (j : Nat) :
    (addV (scale (Q*Q) (signs b) ++ next) residual).getD (2*b.length+j) 0 =
      next.getD j 0 + residual.getD (2*b.length+j) 0 := by
  rw [addV_getD]
  have he : 2*b.length = (scale (Q*Q) (signs b)).length := by simp
  rw [he, getD_append_back]

#print axioms s_front
#print axioms s_back
end CertSound

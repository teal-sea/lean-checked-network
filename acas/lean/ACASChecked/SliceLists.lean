import ACASChecked.BackwardLists
namespace CertSound

theorem getD_drop {α : Type} (xs : List α) (n j : Nat) (d : α) :
    (xs.drop n).getD j d = xs.getD (n+j) d := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [List.drop_succ_cons, ih]
      have he : n+1+j = (n+j)+1 := by omega
      rw [he,List.getD_cons_succ]

theorem getD_take {α : Type} (xs : List α) (n j : Nat) (d : α) (hj : j < n) :
    (xs.take n).getD j d = xs.getD j d := by
  induction xs generalizing n j with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases j with
      | zero => rfl
      | succ j =>
        change (xs.take n).getD j d = xs.getD j d
        exact ih n j (by omega)

theorem slice_head (xs : List Int) (n : Nat) :
    ((xs.drop n).take 1).headD 0 = xs.getD n 0 := by
  have ht : ∀ ys : List Int, (ys.take 1).headD 0 = ys.headD 0 := by
    intro ys
    cases ys <;> rfl
  rw [ht]
  have hd : ∀ ys : List Int, ys.headD 0 = ys.getD 0 0 := by
    intro ys
    cases ys <;> rfl
  rw [hd]
  rw [getD_drop]
  simp

#print axioms getD_drop
#print axioms getD_take
end CertSound

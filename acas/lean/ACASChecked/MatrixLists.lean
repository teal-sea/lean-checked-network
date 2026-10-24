import ACASChecked.BackwardLists
namespace CertSound
open RouteA RouteNC

theorem consRow_nil {n : Nat} (r : Fin n → Int) :
    consRow (List.ofFn r) [] = List.ofFn (fun i => [r i]) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    change [r 0] :: consRow (List.ofFn (fun i => r i.succ)) [] = _
    rw [ih]

theorem consRow_ofFn {n : Nat} (r : Fin n → Int) (acc : Fin n → List Int) :
    consRow (List.ofFn r) (List.ofFn acc) = List.ofFn (fun i => r i :: acc i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
    change (r 0 :: acc 0) :: consRow (List.ofFn (fun i => r i.succ))
      (List.ofFn (fun i => acc i.succ)) = _
    rw [ih]

theorem transpose_ofFn {m n : Nat} (hm : 0 < m) (w : Fin m → Fin n → Int) :
    transpose (List.ofFn (fun i => List.ofFn (w i))) =
      List.ofFn (fun j => List.ofFn (fun i => w i j)) := by
  cases m with
  | zero => omega
  | succ m =>
    induction m with
    | zero =>
      simp only [List.ofFn_succ, List.ofFn_zero]
      change consRow (List.ofFn (w 0)) [] = _
      rw [consRow_nil]
    | succ m ih =>
      rw [List.ofFn_succ]
      change consRow (List.ofFn (w 0))
        (transpose (List.ofFn (fun i => List.ofFn (w i.succ)))) = _
      rw [ih (by omega), consRow_ofFn]
      apply congrArg List.ofFn
      funext j
      simp only [List.ofFn_succ]

#print axioms transpose_ofFn
end CertSound

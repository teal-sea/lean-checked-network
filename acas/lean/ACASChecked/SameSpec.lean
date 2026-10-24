import ACASChecked.Block
namespace RouteA
theorem eqB_spec (a b : Int) (h : eqB a b = true) : a = b := by
 have hz : Int.sub a b = 0 := by
  cases hs : Int.sub a b with
  | ofNat n =>
    have hn : n = 0 := by
     unfold eqB at h
     rw [hs] at h
     change Nat.beq n 0 = true at h
     exact Nat.eq_of_beq_eq_true h
    simpa [hn] using hs
  | negSucc n => simp [eqB, hs] at h
 exact Int.sub_eq_zero.mp hz

theorem same_spec : ∀ (a b : List Int), same a b = true → a = b
 | [], [], _ => rfl
 | [], _::_, h => by contradiction
 | _::_, [], h => by contradiction
 | x::xs, y::ys, h => by
   change (eqB x y && same xs ys) = true at h
   have hh : eqB x y = true ∧ same xs ys = true := by
    cases ha : eqB x y <;> cases hb : same xs ys <;> simp_all
   rw [eqB_spec x y hh.1, same_spec xs ys hh.2]
#print axioms same_spec
end RouteA

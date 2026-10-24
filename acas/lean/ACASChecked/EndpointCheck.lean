import ACASChecked.EndpointRules
namespace CertSound
open RouteA RouteNC

/-- Extract exactly the endpoint equations tested by the executable row traversal. -/
theorem checkEndpoints_extract {m n : Nat} (w : Fin m → Fin n → Int)
    (b l u : Fin m → Int) (il iu : Fin n → Int) (claims : List Int) (first : Bool)
    (h : checkEndpoints (List.ofFn l) (List.ofFn u)
      (List.ofFn (fun j => List.ofFn (w j))) (List.ofFn b)
      (List.ofFn il) (List.ofFn iu) claims first = true) :
    ∀ j : Fin m,
      let p := ibpRow (List.ofFn (w j)) (List.ofFn il) (List.ofFn iu) (b j)
      if first then l j = p.1 / Q ∧ u j = -((-p.2)/Q)
      else l j = max (p.1/Q) (claims.getD (2*j.val) 0 / (Q*Q)) ∧
        u j = min (-((-p.2)/Q)) (-(claims.getD (2*j.val+1) 0 / (Q*Q))) := by
  induction m generalizing claims with
  | zero => exact fun j => j.elim0
  | succ m ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ] at h
    cases first with
    | true =>
      change (eqB _ _ && eqB _ _) && checkEndpoints _ _ _ _ _ _ claims true = true at h
      have hh := Bool.and_eq_true_iff.mp h
      have he := Bool.and_eq_true_iff.mp hh.1
      have hl := eqB_spec _ _ he.1
      have hu := eqB_spec _ _ he.2
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact ⟨hl,hu⟩
      · exact ih (fun j => w j.succ) (fun j => b j.succ) (fun j => l j.succ)
          (fun j => u j.succ) claims hh.2 j
    | false =>
      cases claims with
      | nil => simp [checkEndpoints] at h
      | cons lo cs =>
        cases cs with
        | nil => simp [checkEndpoints] at h
        | cons negHi rest =>
          change (eqB _ _ && (eqB _ _ && decide (l 0 ≤ u 0))) &&
            checkEndpoints _ _ _ _ _ _ rest false = true at h
          have hh := Bool.and_eq_true_iff.mp h
          have he := Bool.and_eq_true_iff.mp hh.1
          have hl := eqB_spec _ _ he.1
          have hu := eqB_spec _ _ (Bool.and_eq_true_iff.mp he.2).1
          intro j
          refine Fin.cases ?_ (fun j => ?_) j
          · exact ⟨hl,hu⟩
          · have hj := ih (fun j => w j.succ) (fun j => b j.succ) (fun j => l j.succ)
              (fun j => u j.succ) rest hh.2 j
            have heven : 2*(j.val+1) = (2*j.val)+1+1 := by omega
            have hodd : 2*(j.val+1)+1 = (2*j.val+1)+1+1 := by omega
            simpa only [Fin.val_succ, heven, hodd, List.getD_cons_succ] using hj

theorem checkEndpoints_sound {m n : Nat} (w : Fin m → Fin n → Int)
    (b l u : Fin m → Int) (il iu : Fin n → Int) (claims : List Int) (first : Bool)
    (h : checkEndpoints (List.ofFn l) (List.ofFn u)
      (List.ofFn (fun j => List.ofFn (w j))) (List.ofFn b)
      (List.ofFn il) (List.ofFn iu) claims first = true)
    (x : Fin n → ℝ) (z : Fin m → ℝ)
    (hx : ∀ i, (il i : ℝ) ≤ x i ∧ x i ≤ (iu i : ℝ))
    (hz : ∀ j, (Q : ℝ)*z j = (b j : ℝ)*(Q : ℝ) + ∑ i, (w j i : ℝ)*x i)
    (hclaims : first = false → ∀ j,
      (claims.getD (2*j.val) 0 : ℝ) ≤ (Q : ℝ)^2*z j ∧
      (claims.getD (2*j.val+1) 0 : ℝ) ≤ -(Q : ℝ)^2*z j) :
    ∀ j, (l j : ℝ) ≤ z j ∧ z j ≤ (u j : ℝ) := by
  intro j
  have he := checkEndpoints_extract w b l u il iu claims first h j
  have hibp := ibp_row_enclosure (w j) il iu (b j) x (z j) hx (hz j)
  dsimp only at he hibp
  cases first with
  | true =>
    simp only [Bool.true_eq, ↓reduceIte] at he
    rw [he.1,he.2]
    exact hibp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at he
    exact endpoint_intersection _ _ _ _ _ _ (z j) hibp
      (hclaims rfl j).1 (hclaims rfl j).2 he.1 he.2

#print axioms checkEndpoints_sound
#print axioms checkEndpoints_extract
end CertSound

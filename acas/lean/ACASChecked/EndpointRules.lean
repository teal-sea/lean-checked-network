import ACASChecked.ListAlgebra
namespace CertSound
open RouteA RouteNC Finset

theorem ibpRow_ofFn {n : Nat} (w l u : Fin n → Int) (b : Int) :
    ibpRow (List.ofFn w) (List.ofFn l) (List.ofFn u) b =
      (b*Q + ∑ i, min (w i*l i) (w i*u i), b*Q + ∑ i, max (w i*l i) (w i*u i)) := by
  induction n with
  | zero => simp [ibpRow, Int.mul_def]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
    change (Int.add (ibpRow _ _ _ b).1 (min (Int.mul (w 0) (l 0)) (Int.mul (w 0) (u 0))),
      Int.add (ibpRow _ _ _ b).2 (max (Int.mul (w 0) (l 0)) (Int.mul (w 0) (u 0)))) = _
    rw [ih]
    simp only [Int.add_def, Int.mul_def, Fin.sum_univ_succ, Prod.mk.injEq]
    constructor <;> ring

theorem mul_endpoints (p l u z : ℝ) (hl : l ≤ z) (hu : z ≤ u) :
    min (p*l) (p*u) ≤ p*z ∧ p*z ≤ max (p*l) (p*u) := by
  rcases le_total 0 p with hp | hp
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hl hp),
      (mul_le_mul_of_nonneg_left hu hp).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hu hp),
      (mul_le_mul_of_nonpos_left hl hp).trans (le_max_left _ _)⟩

theorem Q_eq_pow : Q = (2 : Int)^50 := by norm_num [Q]

theorem Q_pos : (0 : ℝ) < (Q : ℝ) := by norm_num [Q]
theorem Q_ne : Q ≠ 0 := by norm_num [Q]

theorem floor_scaled (n d : Int) (z : ℝ) (hd : 0 < d) (hn : (n : ℝ) ≤ (d : ℝ)*z) :
    ((n / d : Int) : ℝ) ≤ z := by
  have hf := Int.ediv_mul_le n (ne_of_gt hd)
  have hfR : ((n / d : Int) : ℝ) * (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hf
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  nlinarith

theorem ceil_scaled (n d : Int) (z : ℝ) (hd : 0 < d) (hn : (d : ℝ)*z ≤ (n : ℝ)) :
    z ≤ (-(Int.ediv (-n) d) : Int) := by
  have h := floor_scaled (-n) d (-z) hd (by simpa using neg_le_neg hn)
  push_cast
  change z ≤ -(((-n / d : Int) : ℝ))
  linarith

theorem ibp_row_enclosure {n : Nat} (w l u : Fin n → Int) (b : Int)
    (x : Fin n → ℝ) (z : ℝ)
    (hx : ∀ i, (l i : ℝ) ≤ x i ∧ x i ≤ (u i : ℝ))
    (hz : (Q : ℝ)*z = (b : ℝ)*(Q : ℝ) + ∑ i, (w i : ℝ)*x i) :
    let p := ibpRow (List.ofFn w) (List.ofFn l) (List.ofFn u) b
    ((p.1 / Q : Int) : ℝ) ≤ z ∧ z ≤ (-(Int.ediv (-p.2) Q) : Int) := by
  rw [ibpRow_ofFn]
  dsimp only
  have hterms := fun i => mul_endpoints (w i : ℝ) (l i : ℝ) (u i : ℝ) (x i) (hx i).1 (hx i).2
  constructor
  · apply floor_scaled _ Q z (by norm_num [Q])
    push_cast
    rw [hz]
    exact add_le_add (le_refl _) (sum_le_sum (fun i _ => (hterms i).1))
  · apply ceil_scaled _ Q z (by norm_num [Q])
    push_cast
    rw [hz]
    exact add_le_add (le_refl _) (sum_le_sum (fun i _ => (hterms i).2))

/-- Combining an independently established dual bound and IBP enclosure is sound. -/
theorem endpoint_intersection (il iu lo negHi l u : Int) (z : ℝ)
    (hibp : (il : ℝ) ≤ z ∧ z ≤ (iu : ℝ))
    (hlo : (lo : ℝ) ≤ (Q : ℝ)^2*z) (hhi : (negHi : ℝ) ≤ -(Q : ℝ)^2*z)
    (hl : l = max il (lo / (Q*Q))) (hu : u = min iu (-(negHi / (Q*Q)))) :
    (l : ℝ) ≤ z ∧ z ≤ (u : ℝ) := by
  have hq : (0 : Int) < Q*Q := by norm_num [Q]
  have hll := floor_scaled lo (Q*Q) z hq (by simpa [pow_two] using hlo)
  have hhh := floor_scaled negHi (Q*Q) (-z) hq (by simpa [pow_two] using hhi)
  rw [hl,hu]
  push_cast
  exact ⟨max_le hibp.1 hll, le_min hibp.2 (by linarith)⟩

#print axioms ibp_row_enclosure
#print axioms endpoint_intersection
end CertSound

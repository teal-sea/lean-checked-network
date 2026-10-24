import Mathlib
import ACASChecked.NodeNC
namespace CertSound
open Finset

theorem affine_segment (p l u z m : ℝ) (hl : l ≤ z) (hu : z ≤ u)
    (hml : m ≤ p*l) (hmu : m ≤ p*u) : m ≤ p*z := by
  rcases le_total 0 p with hp | hp
  · exact hml.trans (mul_le_mul_of_nonneg_left hl hp)
  · exact hmu.trans (mul_le_mul_of_nonpos_left hu hp)

/-- Endpoint and kink checks suffice for an arbitrary ReLU dual residual. -/
theorem residual_bound (a n l u z m : ℝ) (hl : l ≤ z) (hu : z ≤ u)
    (hml : m ≤ a * max 0 l - n*l) (hmu : m ≤ a * max 0 u - n*u)
    (hm0 : l ≤ 0 ∧ 0 ≤ u → m ≤ 0) :
    m ≤ a * max 0 z - n*z := by
  rcases le_total z 0 with hz | hz
  · have hln : l ≤ 0 := hl.trans hz
    rw [max_eq_left hz]
    by_cases hun : u ≤ 0
    · have hh := affine_segment (-n) l u z m hl hu
        (by simpa [max_eq_left hln] using hml)
        (by simpa [max_eq_left hun] using hmu)
      simpa using hh
    · have hh := affine_segment (-n) l 0 z m hl hz
        (by simpa [max_eq_left hln] using hml)
        (by simpa using hm0 ⟨hln, le_of_lt (lt_of_not_ge hun)⟩)
      simpa using hh
  · have hup : 0 ≤ u := hz.trans hu
    rw [max_eq_right hz]
    by_cases hlp : 0 ≤ l
    · have hh := affine_segment (a-n) l u z m hl hu
        (by simpa only [max_eq_right hlp, sub_mul] using hml)
        (by simpa only [max_eq_right hup, sub_mul] using hmu)
      simpa only [sub_mul] using hh
    · have hh := affine_segment (a-n) 0 u z m hz hu
        (by simpa using hm0 ⟨le_of_lt (lt_of_not_ge hlp), hup⟩)
        (by simpa only [max_eq_right hup, sub_mul] using hmu)
      simpa only [sub_mul] using hh

/-- One telescoping step, in grid-scaled real coordinates. -/
theorem layer_identity {n m : Nat} (q : ℝ)
    (w : Fin m → Fin n → ℝ) (b z : Fin m → ℝ) (y : Fin n → ℝ)
    (a nu : Fin m → ℝ) (c : Fin n → ℝ)
    (hz : ∀ j, q*z j = q*b j + ∑ i, w j i * y i)
    (hc : ∀ i, c i = ∑ j, w j i * nu j) :
    ∑ j, a j * max 0 (z j) =
      q * ∑ j, nu j * b j + ∑ i, c i * y i +
      ∑ j, (a j * max 0 (z j) - nu j * q * z j) := by
  have he : ∑ j, nu j * q * z j =
      q * ∑ j, nu j * b j + ∑ i, c i * y i := by
    simp_rw [mul_assoc, hz, mul_add, mul_sum]
    rw [sum_add_distrib, sum_comm]
    congr 1
    · apply sum_congr rfl
      intro j _
      ring
    · simp_rw [hc, sum_mul]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
  rw [sum_sub_distrib, he]
  ring

theorem layer_lower {n m : Nat} (q : ℝ)
    (w : Fin m → Fin n → ℝ) (b z : Fin m → ℝ) (y : Fin n → ℝ)
    (a nu : Fin m → ℝ) (c : Fin n → ℝ) (r : Fin m → ℝ)
    (hz : ∀ j, q*z j = q*b j + ∑ i, w j i * y i)
    (hc : ∀ i, c i = ∑ j, w j i * nu j)
    (hr : ∀ j, r j ≤ a j * max 0 (z j) - nu j*q*z j) :
    q * ∑ j, nu j * b j + ∑ i, c i * y i + ∑ j, r j ≤
      ∑ j, a j * max 0 (z j) := by
  rw [layer_identity q w b z y a nu c hz hc]
  exact add_le_add (le_refl _) (sum_le_sum (s := univ) (fun j _ => hr j))

#print axioms residual_bound
#print axioms layer_identity
#print axioms layer_lower
end CertSound

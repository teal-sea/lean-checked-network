import ACASChecked.Telescoping
import ACASChecked.BackwardLists
namespace CertSound
open Finset RouteNC

/-- Backward tail sums plus local lower bounds compose without any optimization assumptions. -/
theorem backward_compose (L : Nat) (hL : 0 < L) (s r d : Nat → ℝ) (target : ℝ)
    (hlast : s (L-1) + d (L-1) ≤ target)
    (hs : ∀ k < L-1, s k = s (k+1) + r k)
    (hd : ∀ k < L-1, r k + d k ≤ d (k+1)) : s 0 + d 0 ≤ target := by
  have hb : ∀ n, n < L → s (L-1-n) + d (L-1-n) ≤ target := by
    intro n
    induction n with
    | zero => simpa using fun (_ : 0 < L) => hlast
    | succ n ih =>
      intro hn
      have hip := ih (by omega)
      have hk : L-1-(n+1) < L-1 := by omega
      have he : L-1-(n+1)+1 = L-1-n := by omega
      have hstep := hd _ hk
      rw [he] at hstep
      rw [hs _ hk, he]
      linarith
  simpa using hb (L-1) (by omega)

/-- Endpoint enclosures can be established in dependency order. -/
theorem dependency_order (P : Nat → Prop) (L : Nat)
    (h : ∀ k < L, (∀ j < k, P j) → P k) : ∀ k < L, P k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    exact h k hk (fun j hj => ih j hj (by omega))

/-- Strict integer margin on the grid implies the strict real upper bound. -/
theorem margin_sound (claim thresholdNumer thresholdDen : Int) (value : ℝ)
    (hd : 0 < thresholdDen)
    (hclaim : (claim : ℝ) ≤ -(Q : ℝ)^3*value)
    (hmargin : 0 < claim*thresholdDen + thresholdNumer*(Q*Q*Q)) :
    value < (thresholdNumer : ℝ)/(thresholdDen : ℝ) := by
  have hq := Q_pos
  have hdR : (0 : ℝ) < thresholdDen := by exact_mod_cast hd
  have hm : (0 : ℝ) < (claim : ℝ)*(thresholdDen : ℝ) +
      (thresholdNumer : ℝ)*(Q : ℝ)^3 := by
    exact_mod_cast hmargin
  apply (lt_div_iff₀ hdR).mpr
  by_contra hn
  have hle : (thresholdNumer : ℝ) ≤ value*(thresholdDen : ℝ) := le_of_not_gt hn
  have hh := mul_le_mul_of_nonneg_right hle (pow_nonneg (le_of_lt hq) 3)
  have hc := mul_le_mul_of_nonneg_right hclaim (le_of_lt hdR)
  nlinarith

#print axioms backward_compose
#print axioms dependency_order
#print axioms margin_sound
end CertSound

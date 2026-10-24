import ACASChecked.EndpointRules
namespace CertSound
open Finset

/-- Telescope arbitrary proved inequalities along a finite trace. -/
theorem telescope_lower (r s : Nat → ℝ) (L : Nat)
    (h : ∀ k < L, r k + s k ≤ s (k+1)) :
    (∑ k ∈ range L, r k) + s 0 ≤ s L := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hp := ih (fun k hk => h k (by omega))
    have hl := h L (by omega)
    rw [sum_range_succ]
    linarith

/-- A network prefix uses only enclosures for preactivations in that prefix. -/
theorem dual_prefix_lower (d : Nat → Nat) (L : Nat) (q : ℝ)
    (w : ∀ k, Fin (d (k+1)) → Fin (d k) → ℝ)
    (b z nu : ∀ k, Fin (d (k+1)) → ℝ)
    (y c : ∀ k, Fin (d k) → ℝ) (r : Nat → ℝ)
    (hy : ∀ k < L, ∀ j, y (k+1) j = max 0 (z k j))
    (hz : ∀ k < L, ∀ j, q*z k j = q*b k j + ∑ i, w k j i*y k i)
    (hc : ∀ k < L, ∀ i, c k i = ∑ j, w k j i*nu k j)
    (hr : ∀ k < L, r k ≤ q * ∑ j, nu k j*b k j +
      ∑ j, (c (k+1) j*max 0 (z k j) - nu k j*q*z k j)) :
    (∑ k ∈ range L, r k) + (∑ i, c 0 i*y 0 i) ≤ ∑ j, c L j*y L j := by
  apply telescope_lower r (fun k => ∑ i, c k i*y k i) L
  intro k hk
  have he := layer_identity q (w k) (b k) (z k) (y k) (c (k+1)) (nu k) (c k)
    (hz k hk) (hc k hk)
  simp_rw [hy k hk]
  linarith [hr k hk]

#print axioms dual_prefix_lower
end CertSound

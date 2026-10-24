import ACASChecked.ReceiptComposition
namespace CertSound
open Finset RouteNC

/-- Soundness of an arbitrary checked dual receipt on a network prefix.
All quantities here are grid numerators interpreted in the reals. -/
theorem dual_receipt_sound (d : Nat → Nat) (L : Nat) (hL : 0 < L)
    (w : ∀ k, Fin (d (k+1)) → Fin (d k) → Int)
    (b l u nu : ∀ k, Fin (d (k+1)) → Int)
    (c : ∀ k, Fin (d k) → Int)
    (y : ∀ k, Fin (d k) → ℝ) (z : ∀ k, Fin (d (k+1)) → ℝ)
    (boxl boxu : Fin (d 0) → Int) (r s : Nat → Int) (beta claim : Int) (target : ℝ)
    (hy : ∀ k < L, ∀ j, y (k+1) j = max 0 (z k j))
    (hz : ∀ k < L, ∀ j, (Q : ℝ)*z k j = (Q : ℝ)*(b k j : ℝ) + ∑ i, (w k j i : ℝ)*y k i)
    (hc : ∀ k < L, ∀ i, c k i = ∑ j, w k j i*nu k j)
    (hencl : ∀ k < L, ∀ j, (l k j : ℝ) ≤ z k j ∧ z k j ≤ (u k j : ℝ))
    (hbox : ∀ i, (boxl i : ℝ) ≤ y 0 i ∧ y 0 i ≤ (boxu i : ℝ))
    (hr : ∀ k < L, r k = ∑ j, (minZ (l k j) (u k j) (c (k+1) j) (nu k j) + b k j*Q*nu k j))
    (hs : ∀ k < L-1, s k = s (k+1) + r k)
    (hlast : s (L-1) = beta + r (L-1))
    (hclaim : claim = s 0 + ∑ i, min (c 0 i*boxl i) (c 0 i*boxu i))
    (htarget : (beta : ℝ) + ∑ j, (c L j : ℝ)*y L j = target) :
    (claim : ℝ) ≤ target := by
  have hstep : ∀ k < L, (r k : ℝ) + ∑ i, (c k i : ℝ)*y k i ≤
      ∑ j, (c (k+1) j : ℝ)*y (k+1) j := by
    intro k hk
    have hp : ∀ i, (c k i : ℝ) = ∑ j, (w k j i : ℝ)*(nu k j : ℝ) := by
      intro i
      exact_mod_cast hc k hk i
    have he := layer_identity (Q : ℝ) (fun j i => (w k j i : ℝ))
      (fun j => (b k j : ℝ)) (z k) (y k) (fun j => (c (k+1) j : ℝ))
      (fun j => (nu k j : ℝ)) (fun i => (c k i : ℝ)) (hz k hk) hp
    have hm : ∀ j, (minZ (l k j) (u k j) (c (k+1) j) (nu k j) : ℝ) ≤
        (c (k+1) j : ℝ)*max 0 (z k j) - (nu k j : ℝ)*(Q : ℝ)*z k j := by
      intro j
      exact minZ_sound _ _ _ _ _ (hencl k hk j).1 (hencl k hk j).2
    have hrr : (r k : ℝ) ≤ (Q : ℝ) * ∑ j, (nu k j : ℝ)*(b k j : ℝ) +
        ∑ j, ((c (k+1) j : ℝ)*max 0 (z k j) - (nu k j : ℝ)*(Q : ℝ)*z k j) := by
      rw [hr k hk]
      push_cast
      rw [mul_sum, ← sum_add_distrib]
      apply sum_le_sum
      intro j _
      nlinarith [hm j]
    simp_rw [hy k hk]
    linarith
  have hsum : ∀ k < L, (s k : ℝ) + ∑ i, (c k i : ℝ)*y k i ≤ target := by
    intro k hk
    -- Apply the same trace composition starting at the requested coordinate.
    have hb : ∀ n, n < L → (s (L-1-n) : ℝ) +
        ∑ i, (c (L-1-n) i : ℝ)*y (L-1-n) i ≤ target := by
      intro n
      induction n with
      | zero =>
        intro _
        have hp := hstep (L-1) (by omega)
        have hidx : L-1+1 = L := by omega
        rw [hidx] at hp
        have hsl : (s (L-1) : ℝ) = (beta : ℝ) + (r (L-1) : ℝ) := by exact_mod_cast hlast
        simp only [Nat.sub_zero]
        linarith
      | succ n ih =>
        intro hn
        have hp := ih (by omega)
        have hidx : L-1-(n+1)+1 = L-1-n := by omega
        have hkk : L-1-(n+1) < L-1 := by omega
        have hsR : (s (L-1-(n+1)) : ℝ) = (s (L-1-n) : ℝ) + (r (L-1-(n+1)) : ℝ) := by
          rw [hs _ hkk, hidx]
          push_cast
          rfl
        have hh := hstep (L-1-(n+1)) (by omega)
        rw [hidx] at hh
        linarith
    have hh := hb (L-1-k) (by omega)
    have he : L-1-(L-1-k) = k := by omega
    exact (congrArg (fun k => (s k : ℝ) + ∑ i, (c k i : ℝ)*y k i ≤ target) he).mp hh
  rw [hclaim]
  push_cast
  apply le_trans _ (hsum 0 hL)
  apply add_le_add (le_refl _)
  apply sum_le_sum
  intro i _
  have hh := mul_endpoints (c 0 i : ℝ) (boxl i : ℝ) (boxu i : ℝ) (y 0 i) (hbox i).1 (hbox i).2
  exact hh.1

#print axioms dual_receipt_sound
end CertSound

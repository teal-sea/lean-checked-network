import Mathlib
open Finset
namespace RouteA
theorem packed_inj (B K : Int) (hB : 2 * K < B) : ∀ (n : Nat) (a b : Fin n → Int),
    (∀ i, |a i| ≤ K) → (∀ i, |b i| ≤ K) →
    ∑ i, a i * B ^ (i : Nat) = ∑ i, b i * B ^ (i : Nat) → ∀ i, a i = b i
  | 0, _, _, _, _, _, i => i.elim0
  | n + 1, a, b, ha, hb, hs, i => by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hs
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ] at hs
    have hfac : ∀ c : Fin (n + 1) → Int,
        ∑ i : Fin n, c i.succ * (B ^ (i : Nat) * B) = B * ∑ i : Fin n, c i.succ * B ^ (i : Nat) := by
      intro c; rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    rw [hfac a, hfac b] at hs
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (ha 0)
    have hB0 : B ≠ 0 := by omega
    have h0 : a 0 = b 0 := by
      have hdvd : B ∣ a 0 - b 0 :=
        ⟨(∑ i : Fin n, b i.succ * B ^ (i : Nat)) - ∑ i : Fin n, a i.succ * B ^ (i : Nat), by
          rw [mul_sub]; linarith⟩
      have hlt : |a 0 - b 0| < B := by
        have h1 := ha 0; have h2 := hb 0
        rw [abs_le] at h1 h2; rw [abs_lt]; constructor <;> linarith
      have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
      linarith
    have hrest : ∑ i : Fin n, a i.succ * B ^ (i : Nat) = ∑ i : Fin n, b i.succ * B ^ (i : Nat) :=
      mul_left_cancel₀ hB0 (by linarith)
    have ih := packed_inj B K hB n (fun i => a i.succ) (fun i => b i.succ) (fun _ => ha _)
      (fun _ => hb _) hrest
    exact Fin.cases h0 (fun i => ih i) i


end RouteA

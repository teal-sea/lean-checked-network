import PhaseGrid.FullSet

/-!
# All frequencies at an even modulus, and the statement for every modulus

For `p = 2m ≥ 4` and `S = [1, …, m − 1]`, every nonzero shift `s` has wave sum
`(−1 − cos(πs))/2 ≤ 0`, so `g = |S|` is a gap and `M ≥ 25` suffices (`adds_mod_p_full_even`).
Together with the odd case: for every `p ≥ 3`, all frequencies `1, …, ⌊(p − 1)/2⌋` and every
`M ≥ 25`, the integer network adds mod `p` (`adds_mod_p_full`).
-/

namespace PhaseGrid
open Real

/-- Splitting a sum over `0, …, 2m − 1` into the terms `0` and `m` and two mirrored halves:
`f (m + x + 1) = f (m − 1 − x)` for `x < m − 1`. -/
theorem sum_split_even (f : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hsym : ∀ x, x < m - 1 → f (m + x + 1) = f (m - 1 - x)) :
    ∑ k ∈ Finset.range (2 * m), f k = f 0 + f m + 2 * ∑ k ∈ Finset.range (m - 1), f (k + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hsym ⊢
  rw [show 2 * (n + 1) = (n + 1) + (n + 1) by ring, Finset.sum_range_add, Finset.sum_range_succ',
    Finset.sum_range_succ']
  have : ∑ x ∈ Finset.range n, f (n + 1 + (x + 1)) = ∑ x ∈ Finset.range n, f (x + 1) := by
    rw [← Finset.sum_range_reflect (fun k => f (k + 1)) n]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    rw [show n + 1 + (x + 1) = (n + 1) + x + 1 by ring, hsym x hx]
    congr 1
    omega
  rw [this, Nat.add_zero]
  ring

/-- For even `p = 2m` and `0 < s < p`: `Σ_{k=1}^{m−1} cos(2πks/p) = (−1 − cos(πs))/2 ≤ 0`. -/
theorem sum_cos_even_le (m s : ℕ) (hm : 1 ≤ m) (hs0 : 0 < s) (hsp : s < 2 * m) :
    ∑ k ∈ Finset.range (m - 1), cos (2 * π * ((k + 1 : ℕ) : ℝ) * s / ((2 * m : ℕ) : ℝ)) ≤ 0 := by
  have hp : ((2 * m : ℕ) : ℝ) ≠ 0 := by
    have : 0 < 2 * m := by omega
    exact_mod_cast this.ne'
  have h0 := sum_cos_range_eq_zero (2 * m) s hs0 hsp
  rw [sum_split_even (fun k => cos (2 * π * (k : ℝ) * s / ((2 * m : ℕ) : ℝ))) m hm ?_] at h0
  · simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, cos_zero] at h0
    have := Real.neg_one_le_cos (2 * π * (m : ℝ) * s / ((2 * m : ℕ) : ℝ))
    linarith
  · intro x hx
    show cos (2 * π * ((m + x + 1 : ℕ) : ℝ) * s / ((2 * m : ℕ) : ℝ))
      = cos (2 * π * ((m - 1 - x : ℕ) : ℝ) * s / ((2 * m : ℕ) : ℝ))
    rw [show m + x + 1 = 2 * m - (m - 1 - x) by omega]
    exact cos_reflect (2 * m) (m - 1 - x) s (by omega) hp

/-- At even `p = 2m` with all frequencies `1, …, m − 1`, every nonzero shift has wave sum `≤ 0`. -/
theorem waveSum_full_even (m s : ℕ) (hm : 1 ≤ m) (hs0 : 0 < s) (hsp : s < 2 * m) :
    waveSum (2 * m) (List.range' 1 (m - 1)) s ≤ 0 := by
  rw [waveSum_range']
  have := sum_cos_even_le m s hm hs0 hsp
  calc _ = ∑ k ∈ Finset.range (m - 1), cos (2 * π * ((k + 1 : ℕ) : ℝ) * s / ((2 * m : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.add_comm 1 k]
    _ ≤ 0 := this

/-- **Every even modulus.** For `p = 2m ≥ 4`, the frequencies `1, …, m − 1` and any scale `M ≥ 25`,
the integer phase-grid network adds mod `p` on every pair. -/
theorem adds_mod_p_full_even (m : ℕ) (hm : 2 ≤ m) (M : ℕ) (hM : 25 ≤ M) :
    ∀ a, a < 2 * m → ∀ b, b < 2 * m →
      answer (2 * m) (List.range' 1 (m - 1)) M a b = (a + b) % (2 * m) := by
  apply adds_mod_p (2 * m) (by omega) (List.range' 1 (m - 1)) M ((m - 1 : ℕ) : ℝ)
  · intro s hs0 hsp
    rw [List.length_range']
    have := waveSum_full_even m s (by omega) hs0 hsp
    linarith
  · rw [List.length_range']
    have h25 : (25 : ℝ) ≤ M := by exact_mod_cast hM
    have hm' : (1 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m - 1 by omega)
    nlinarith

/-- **Every modulus `p ≥ 3`**, all frequencies `1, …, ⌊(p − 1)/2⌋`, every scale `M ≥ 25`: the integer
phase-grid network answers `(a + b) % p` on every pair `a, b < p`. The proposal's headline claim
("5-bit weights add mod p for every modulus"), kernel-checked. -/
theorem adds_mod_p_full (p : ℕ) (hp : 3 ≤ p) (M : ℕ) (hM : 25 ≤ M) :
    ∀ a, a < p → ∀ b, b < p → answer p (List.range' 1 ((p - 1) / 2)) M a b = (a + b) % p := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' p
  · subst hm
    rw [show (2 * m - 1) / 2 = m - 1 by omega]
    exact adds_mod_p_full_even m (by omega) M hM
  · subst hm
    rw [show (2 * m + 1 - 1) / 2 = m by omega]
    exact adds_mod_p_full_odd m (by omega) M (by omega)

end PhaseGrid

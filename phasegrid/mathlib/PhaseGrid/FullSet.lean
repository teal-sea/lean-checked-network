import PhaseGrid.Score

/-!
# All frequencies at an odd modulus: the gap is p/2, so M = 24 is enough

For `p = 2m + 1` and `S = [1, …, m]`, every nonzero shift `s` has wave sum `−1/2`
(`sum_cos_range_eq_zero`: the `p` roots of unity sum to zero; `sum_cos_half`: the frequencies `k` and
`p − k` carry the same cosine). So the gap is `m + 1/2 = p/2`, and `24 |S| = 24 m < 24 (2m + 1)/2 ≤
M p / 2` for every `M ≥ 24`: the integer network adds mod `p` (`adds_mod_p_full_odd`). The proposal
said `M ≥ 25`; for odd `p` its own bound already gives `M ≥ 24`, and `25` is only needed for even `p`.
-/

namespace PhaseGrid
open Real

/-- The `p` roots of unity `e^{2πiks/p}`, `k < p`, sum to zero when `0 < s < p`; taking real parts,
`Σ_{k<p} cos(2πks/p) = 0`. -/
theorem sum_cos_range_eq_zero (p s : ℕ) (hs0 : 0 < s) (hsp : s < p) :
    ∑ k ∈ Finset.range p, cos (2 * π * k * s / p) = 0 := by
  have hp0 : 0 < p := by omega
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  set ζ : ℂ := Complex.exp (((2 * π * s / p : ℝ) : ℂ) * Complex.I) with hζ
  have hζp : ζ ^ p = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    rw [show (p : ℂ) * (((2 * π * s / p : ℝ) : ℂ) * Complex.I) = ((s : ℤ) : ℂ) * (2 * π * Complex.I) by
      push_cast; field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have hζ1 : ζ ≠ 1 := by
    rw [hζ, Ne, Complex.exp_eq_one_iff]
    rintro ⟨n, hn⟩
    have h1 : ((2 * π * s / p : ℝ) : ℂ) * Complex.I = ((n * (2 * π) : ℝ) : ℂ) * Complex.I := by
      rw [hn]; push_cast; ring
    have h2 : (2 * π * s / p : ℝ) = n * (2 * π) := by
      have := congrArg Complex.im h1
      simpa using this
    have h3 : (s : ℝ) = n * p := by
      field_simp at h2
      linarith [h2]
    have h4 : (s : ℤ) = n * p := by exact_mod_cast h3
    have hp' : (0 : ℤ) < p := by omega
    have hn0 : 0 < n := by
      by_contra h
      have : n * (p : ℤ) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hp'.le
      omega
    have hn1 : n < 1 := by
      by_contra h
      have : (p : ℤ) ≤ n * p := by nlinarith [not_lt.mp h]
      omega
    omega
  have hsum : ∑ k ∈ Finset.range p, ζ ^ k = 0 := by
    rw [geom_sum_eq hζ1, hζp, sub_self, zero_div]
  have hre : ∀ k : ℕ, (ζ ^ k).re = cos (2 * π * k * s / p) := by
    intro k
    rw [hζ, ← Complex.exp_nat_mul,
      show (k : ℂ) * (((2 * π * s / p : ℝ) : ℂ) * Complex.I) = ((2 * π * k * s / p : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
    exact Complex.exp_ofReal_mul_I_re _
  have := congrArg Complex.re hsum
  rw [Complex.re_sum] at this
  simp only [hre, Complex.zero_re] at this
  exact this

/-- The frequencies `k` and `p − k` give the same cosine. -/
theorem cos_reflect (p k s : ℕ) (hk : k ≤ p) (hp : (p : ℝ) ≠ 0) :
    cos (2 * π * ((p - k : ℕ) : ℝ) * s / p) = cos (2 * π * k * s / p) := by
  rw [Nat.cast_sub hk]
  rw [show 2 * π * ((p : ℝ) - k) * s / p = (s : ℕ) * (2 * π) - 2 * π * k * s / p by
    field_simp]
  exact cos_nat_mul_two_pi_sub _ _

/-- Splitting a sum over `0, …, 2m` into the term `0` and the two halves, when the second half
mirrors the first: `f (m + x + 1) = f (m − x)`. -/
theorem sum_split_odd (f : ℕ → ℝ) (m : ℕ) (hsym : ∀ x, x < m → f (m + x + 1) = f (m - x)) :
    ∑ k ∈ Finset.range (2 * m + 1), f k = f 0 + 2 * ∑ k ∈ Finset.range m, f (k + 1) := by
  rw [Finset.sum_range_succ', show 2 * m = m + m from two_mul m, Finset.sum_range_add]
  have : ∑ x ∈ Finset.range m, f (m + x + 1) = ∑ x ∈ Finset.range m, f (x + 1) := by
    rw [← Finset.sum_range_reflect (fun k => f (k + 1)) m]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    rw [hsym x hx]
    congr 1
    omega
  rw [this]
  ring

/-- For odd `p = 2m + 1` and `0 < s < p`: `Σ_{k=1}^{m} cos(2πks/p) = −1/2`. -/
theorem sum_cos_half (m s : ℕ) (hs0 : 0 < s) (hsp : s < 2 * m + 1) :
    ∑ k ∈ Finset.range m, cos (2 * π * ((k + 1 : ℕ) : ℝ) * s / ((2 * m + 1 : ℕ) : ℝ)) = -1 / 2 := by
  have hp : ((2 * m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h0 := sum_cos_range_eq_zero (2 * m + 1) s hs0 hsp
  rw [sum_split_odd (fun k => cos (2 * π * (k : ℝ) * s / ((2 * m + 1 : ℕ) : ℝ))) m ?_] at h0
  · simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, cos_zero] at h0
    linarith
  · intro x hx
    show cos (2 * π * ((m + x + 1 : ℕ) : ℝ) * s / ((2 * m + 1 : ℕ) : ℝ))
      = cos (2 * π * ((m - x : ℕ) : ℝ) * s / ((2 * m + 1 : ℕ) : ℝ))
    rw [show m + x + 1 = (2 * m + 1) - (m - x) by omega]
    exact cos_reflect (2 * m + 1) (m - x) s (by omega) hp

/-- The wave sum over the list `[a, …, a + m − 1]` as a `Finset` sum. -/
theorem waveSum_range' (p : ℕ) (a m : ℕ) (s : ℝ) :
    waveSum p (List.range' a m) s
      = ∑ k ∈ Finset.range m, cos (2 * π * ((a + k : ℕ) : ℝ) * s / p) := by
  unfold waveSum
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    rw [List.range'_succ, List.map_cons, List.sum_cons, ih (a + 1), Finset.sum_range_succ', add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [show a + 1 + k = a + (k + 1) by omega]

/-- At odd `p = 2m + 1` with all frequencies `1, …, m`, every nonzero shift has wave sum `−1/2`. -/
theorem waveSum_full_odd (m s : ℕ) (hs0 : 0 < s) (hsp : s < 2 * m + 1) :
    waveSum (2 * m + 1) (List.range' 1 m) s = -1 / 2 := by
  rw [waveSum_range', ← sum_cos_half m s hs0 hsp]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.add_comm 1 k]

/-- **Every odd modulus.** For `p = 2m + 1 ≥ 3`, the frequencies `1, …, m` and any scale `M ≥ 24`,
the integer phase-grid network adds mod `p` on every pair. -/
theorem adds_mod_p_full_odd (m : ℕ) (hm : 1 ≤ m) (M : ℕ) (hM : 24 ≤ M) :
    ∀ a, a < 2 * m + 1 → ∀ b, b < 2 * m + 1 →
      answer (2 * m + 1) (List.range' 1 m) M a b = (a + b) % (2 * m + 1) := by
  apply adds_mod_p (2 * m + 1) (by omega) (List.range' 1 m) M (((2 * m + 1 : ℕ) : ℝ) / 2)
  · intro s hs0 hsp
    rw [waveSum_full_odd m s hs0 hsp, List.length_range']
    push_cast; linarith
  · rw [List.length_range']
    have h24 : (24 : ℝ) ≤ M := by exact_mod_cast hM
    have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    nlinarith

/-- The two all-frequency instances kernel-checked as explicit tables in stage 3, as corollaries. -/
theorem adds_mod_7_full (M : ℕ) (hM : 24 ≤ M) :
    ∀ a, a < 7 → ∀ b, b < 7 → answer 7 (List.range' 1 3) M a b = (a + b) % 7 :=
  adds_mod_p_full_odd 3 (by norm_num) M hM

theorem adds_mod_113_full (M : ℕ) (hM : 24 ≤ M) :
    ∀ a, a < 113 → ∀ b, b < 113 → answer 113 (List.range' 1 56) M a b = (a + b) % 113 :=
  adds_mod_p_full_odd 56 (by norm_num) M hM

end PhaseGrid

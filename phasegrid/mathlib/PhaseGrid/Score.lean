import PhaseGrid.Defs
import PhaseGrid.ListLemmas

/-!
# The phase-grid network adds mod p (stage 2, parts i to iv)

* `realScore_eq` (i): the real score is one wave, `4 Σ_{k ∈ S} cos(2πk(a + b − c)/p)`.
* `waveSum_right`, `waveSum_wrong` (ii): at the right answer the wave sum is `|S|`; at any wrong
  answer it is at most `|S| − g` when `g` is a gap for `S`.
* `neuron_bound`, `intScore_close` (iii): each neuron's integer term is within `6M²` of `M³` times its
  real term, so the integer score is within `48 M² |S|` of `M³` times the real score.
* `intScore_lt`, `adds_mod_p` (iv): with `24 |S| < M g` the right answer's integer score is strictly
  the largest, so `answer` returns `(a + b) % p` for every pair.
-/

namespace PhaseGrid
open Real

/-! ### (i) The real score is one wave -/

theorem realScore_eq (p : ℕ) (S : List ℕ) (a b c : ℕ) :
    realScore p S a b c = 4 * waveSum p S ((a : ℝ) + b - c) := by
  unfold realScore waveSum
  induction S with
  | nil => simp [neurons]
  | cons k S ih =>
    rw [neurons_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons,
      List.map_map]
    have h := octet (θ p k a) (θ p k b) (θ p k c)
    rw [show ((fun n => rW2 p c n * (rE1 p a n + rE2 p b n) ^ 2) ∘ fun jl : ℕ × ℕ => (k, jl.1, jl.2))
        = fun jl => cos (θ p k c + jl.1 * (π / 2) + jl.2 * (π / 2)) *
          (cos (θ p k a + jl.1 * (π / 2)) + cos (θ p k b + jl.2 * (π / 2))) ^ 2 from rfl, h]
    rw [show θ p k a + θ p k b - θ p k c = 2 * π * k * ((a : ℝ) + b - c) / p by unfold θ; ring]
    ring

/-! ### (ii) The gap -/

/-- At the right answer every wave is at its peak: the wave sum is `|S|`. -/
theorem waveSum_right (p : ℕ) (hp : 0 < p) (S : List ℕ) (a b : ℕ) :
    waveSum p S ((a : ℝ) + b - ((a + b) % p : ℕ)) = S.length := by
  unfold waveSum
  have hq : (a : ℝ) + b - ((a + b) % p : ℕ) = p * ((a + b) / p : ℕ) := by
    have h := Nat.mod_add_div (a + b) p
    have h' : ((a + b : ℕ) : ℝ) = (((a + b) % p : ℕ) : ℝ) + (p : ℝ) * (((a + b) / p : ℕ) : ℝ) := by
      exact_mod_cast h.symm
    push_cast at h'
    linarith
  rw [hq]
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have h1 : ∀ k ∈ S, cos (2 * π * k * ((p : ℝ) * ((a + b) / p : ℕ)) / p) = 1 := by
    intro k _
    rw [show 2 * π * k * ((p : ℝ) * ((a + b) / p : ℕ)) / p = ((k * ((a + b) / p) : ℕ) : ℝ) * (2 * π) by
      push_cast; field_simp]
    exact cos_nat_mul_two_pi _
  rw [List.map_congr_left h1, List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one]

/-- Shifting `s` by a multiple of `p` does not change the wave sum. -/
theorem waveSum_shift (p : ℕ) (hp : 0 < p) (S : List ℕ) (r : ℝ) (q : ℤ) :
    waveSum p S (r + p * q) = waveSum p S r := by
  unfold waveSum
  congr 1
  apply List.map_congr_left
  intro k _
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [show 2 * π * (k : ℝ) * (r + p * q) / p = 2 * π * (k : ℝ) * r / p + (((k : ℤ) * q : ℤ) : ℝ) * (2 * π) by
    push_cast; field_simp]
  exact cos_add_int_mul_two_pi _ _

/-- At a wrong answer `c` the shift `a + b − c` is not a multiple of `p`, so the wave sum is at most
`|S| − g`. -/
theorem waveSum_wrong (p : ℕ) (hp : 0 < p) (S : List ℕ) (g : ℝ)
    (hg : ∀ s : ℕ, 0 < s → s < p → waveSum p S s ≤ S.length - g)
    (a b c : ℕ) (hc : c < p) (hne : c ≠ (a + b) % p) :
    waveSum p S ((a : ℝ) + b - c) ≤ S.length - g := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have hr0 : 0 ≤ ((a : ℤ) + b - c) % p := Int.emod_nonneg _ hp0
  have hrp : ((a : ℤ) + b - c) % p < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp)
  have hrne : ((a : ℤ) + b - c) % p ≠ 0 := by
    intro h0
    apply hne
    have h1 : ((a + b : ℕ) : ℤ) % p = (c : ℤ) % p := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]; push_cast; exact h0
    have h2 : (c : ℤ) % p = c := Int.emod_eq_of_lt (by omega) (by exact_mod_cast hc)
    rw [h2, ← Int.natCast_mod] at h1
    exact_mod_cast h1.symm
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = ((a : ℤ) + b - c) % p :=
    ⟨(((a : ℤ) + b - c) % p).toNat, Int.toNat_of_nonneg hr0⟩
  have hdecomp : (a : ℝ) + b - c = r + p * ((((a : ℤ) + b - c) / p : ℤ) : ℝ) := by
    have h := Int.emod_add_mul_ediv ((a : ℤ) + b - c) p
    rw [← hr] at h
    have h' : ((r : ℤ) : ℝ) + ((p : ℤ) : ℝ) * ((((a : ℤ) + b - c) / p : ℤ) : ℝ) = (((a : ℤ) + b - c : ℤ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    linarith
  rw [hdecomp, waveSum_shift p hp]
  exact hg r (by omega) (by omega)

/-! ### (iii) Rounding -/

/-- `|round(M e)| ≤ M` when `|e| ≤ 1`: the rounded value is an integer at most `M + 1/2`. -/
theorem abs_round_le (M : ℕ) (e : ℝ) (he : |e| ≤ 1) : |((round ((M : ℝ) * e) : ℤ) : ℝ)| ≤ M := by
  have h1 : |(M : ℝ) * e - round ((M : ℝ) * e)| ≤ 1 / 2 := abs_sub_round _
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hMe : |(M : ℝ) * e| ≤ M := by
    rw [abs_mul, abs_of_nonneg hM]
    calc (M : ℝ) * |e| ≤ M * 1 := mul_le_mul_of_nonneg_left he hM
      _ = M := mul_one _
  have h2 : |((round ((M : ℝ) * e) : ℤ) : ℝ)| ≤ M + 1 / 2 := by
    calc |((round ((M : ℝ) * e) : ℤ) : ℝ)|
        = |(M : ℝ) * e - ((M : ℝ) * e - round ((M : ℝ) * e))| := by congr 1; ring
      _ ≤ |(M : ℝ) * e| + |(M : ℝ) * e - round ((M : ℝ) * e)| := abs_sub _ _
      _ ≤ M + 1 / 2 := add_le_add hMe h1
  rw [abs_le] at h2 ⊢
  obtain ⟨h2l, h2r⟩ := h2
  constructor
  · have : (-(M : ℤ) - 1 : ℤ) < round ((M : ℝ) * e) := by
      have : ((-(M : ℤ) - 1 : ℤ) : ℝ) < ((round ((M : ℝ) * e) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have : -(M : ℤ) ≤ round ((M : ℝ) * e) := by omega
    exact_mod_cast this
  · have : round ((M : ℝ) * e) < (M : ℤ) + 1 := by
      have : ((round ((M : ℝ) * e) : ℤ) : ℝ) < (((M : ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have : round ((M : ℝ) * e) ≤ (M : ℤ) := by omega
    exact_mod_cast this

/-- One neuron: with `w' = round(Mw)`, `x = round(Me₁) + round(Me₂)`, `X = Me₁ + Me₂`, the integer
term `w' x²` is within `6M²` of `M w X² = M³ w (e₁ + e₂)²`, because
`w' x² − Mw X² = (w' − Mw) x² + Mw (x − X)(x + X)` with `|w' − Mw| ≤ 1/2`, `|x| ≤ 2M`,
`|x − X| ≤ 1`, `|x + X| ≤ 4M`, `|Mw| ≤ M`. -/
theorem neuron_bound (M : ℕ) (w e1 e2 : ℝ) (hw : |w| ≤ 1) (h1 : |e1| ≤ 1) (h2 : |e2| ≤ 1) :
    |((round ((M : ℝ) * w) : ℤ) : ℝ) *
        ((((round ((M : ℝ) * e1) : ℤ) : ℝ) + ((round ((M : ℝ) * e2) : ℤ) : ℝ)) *
          (((round ((M : ℝ) * e1) : ℤ) : ℝ) + ((round ((M : ℝ) * e2) : ℤ) : ℝ)))
      - (M : ℝ) ^ 3 * (w * (e1 + e2) ^ 2)| ≤ 6 * (M : ℝ) ^ 2 := by
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hw' : |((round ((M : ℝ) * w) : ℤ) : ℝ) - M * w| ≤ 1 / 2 := by
    rw [abs_sub_comm]; exact abs_sub_round _
  have hx : |((round ((M : ℝ) * e1) : ℤ) : ℝ) + ((round ((M : ℝ) * e2) : ℤ) : ℝ)| ≤ 2 * M := by
    calc _ ≤ |((round ((M : ℝ) * e1) : ℤ) : ℝ)| + |((round ((M : ℝ) * e2) : ℤ) : ℝ)| := abs_add_le _ _
      _ ≤ M + M := add_le_add (abs_round_le M e1 h1) (abs_round_le M e2 h2)
      _ = 2 * M := by ring
  have hX : |(M : ℝ) * e1 + M * e2| ≤ 2 * M := by
    calc _ ≤ |(M : ℝ) * e1| + |(M : ℝ) * e2| := abs_add_le _ _
      _ ≤ M * 1 + M * 1 := by
        apply add_le_add
        · rw [abs_mul, abs_of_nonneg hM]; exact mul_le_mul_of_nonneg_left h1 hM
        · rw [abs_mul, abs_of_nonneg hM]; exact mul_le_mul_of_nonneg_left h2 hM
      _ = 2 * M := by ring
  have hxX : |(((round ((M : ℝ) * e1) : ℤ) : ℝ) + ((round ((M : ℝ) * e2) : ℤ) : ℝ))
      - ((M : ℝ) * e1 + M * e2)| ≤ 1 := by
    calc _ = |(((round ((M : ℝ) * e1) : ℤ) : ℝ) - M * e1) + (((round ((M : ℝ) * e2) : ℤ) : ℝ) - M * e2)| := by
          congr 1; ring
      _ ≤ |((round ((M : ℝ) * e1) : ℤ) : ℝ) - M * e1| + |((round ((M : ℝ) * e2) : ℤ) : ℝ) - M * e2| :=
          abs_add_le _ _
      _ ≤ 1 / 2 + 1 / 2 := add_le_add (by rw [abs_sub_comm]; exact abs_sub_round _)
          (by rw [abs_sub_comm]; exact abs_sub_round _)
      _ = 1 := by norm_num
  have hxpX : |(((round ((M : ℝ) * e1) : ℤ) : ℝ) + ((round ((M : ℝ) * e2) : ℤ) : ℝ))
      + ((M : ℝ) * e1 + M * e2)| ≤ 4 * M := by
    calc |(((round ((M : ℝ) * e1) : ℤ) : ℝ) + ((round ((M : ℝ) * e2) : ℤ) : ℝ)) + ((M : ℝ) * e1 + M * e2)|
        ≤ |((round ((M : ℝ) * e1) : ℤ) : ℝ) + ((round ((M : ℝ) * e2) : ℤ) : ℝ)| + |(M : ℝ) * e1 + M * e2| :=
          abs_add_le _ _
      _ ≤ 2 * M + 2 * M := add_le_add hx hX
      _ = 4 * M := by ring
  have hMw : |(M : ℝ) * w| ≤ M := by
    rw [abs_mul, abs_of_nonneg hM]
    calc (M : ℝ) * |w| ≤ M * 1 := mul_le_mul_of_nonneg_left hw hM
      _ = M := mul_one _
  set w' : ℝ := ((round ((M : ℝ) * w) : ℤ) : ℝ) with hw'def
  set x : ℝ := ((round ((M : ℝ) * e1) : ℤ) : ℝ) + ((round ((M : ℝ) * e2) : ℤ) : ℝ) with hxdef
  set X : ℝ := (M : ℝ) * e1 + M * e2 with hXdef
  have key : w' * (x * x) - (M : ℝ) ^ 3 * (w * (e1 + e2) ^ 2)
      = (w' - M * w) * (x * x) + (M * w) * ((x - X) * (x + X)) := by
    rw [hXdef]; ring
  rw [key]
  calc |(w' - M * w) * (x * x) + (M * w) * ((x - X) * (x + X))|
      ≤ |(w' - M * w) * (x * x)| + |(M * w) * ((x - X) * (x + X))| := abs_add_le _ _
    _ ≤ 1 / 2 * ((2 * M) * (2 * M)) + M * (1 * (4 * M)) := by
        apply add_le_add
        · rw [abs_mul, abs_mul]
          exact mul_le_mul hw' (mul_le_mul hx hx (abs_nonneg _) (by positivity)) (by positivity)
            (by norm_num)
        · rw [abs_mul]
          exact mul_le_mul hMw (by rw [abs_mul]; exact mul_le_mul hxX hxpX (abs_nonneg _) (by positivity))
            (abs_nonneg _) hM
    _ = 6 * (M : ℝ) ^ 2 := by ring

theorem abs_list_sum_le (l : List ℝ) : |l.sum| ≤ (l.map abs).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (abs_add_le _ _).trans (add_le_add (le_refl _) ih)

theorem list_sum_sub {α : Type} (l : List α) (f g : α → ℝ) :
    (l.map f).sum - (l.map g).sum = (l.map fun x => f x - g x).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons]; linarith [ih]

theorem list_sum_mul_left {α : Type} (l : List α) (r : ℝ) (f : α → ℝ) :
    r * (l.map f).sum = (l.map fun x => r * f x).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

theorem abs_rE1_le_one (p a : ℕ) (n : ℕ × ℕ × ℕ) : |rE1 p a n| ≤ 1 := abs_cos_le_one _
theorem abs_rE2_le_one (p b : ℕ) (n : ℕ × ℕ × ℕ) : |rE2 p b n| ≤ 1 := abs_cos_le_one _
theorem abs_rW2_le_one (p c : ℕ) (n : ℕ × ℕ × ℕ) : |rW2 p c n| ≤ 1 := abs_cos_le_one _

/-- The integer score is within `48 M² |S|` of `M³` times the real score (`8|S|` neurons, `6M²` each). -/
theorem intScore_close (p : ℕ) (S : List ℕ) (M : ℕ) (a b c : ℕ) :
    |((intScore p S M a b c : ℤ) : ℝ) - (M : ℝ) ^ 3 * realScore p S a b c|
      ≤ 48 * (M : ℝ) ^ 2 * S.length := by
  unfold intScore realScore
  rw [Int.cast_list_sum, List.map_map, list_sum_mul_left, list_sum_sub]
  refine (abs_list_sum_le _).trans ?_
  refine (List.sum_le_length_nsmul _ (6 * (M : ℝ) ^ 2) ?_).trans ?_
  · intro y hy
    simp only [List.map_map, List.mem_map, Function.comp] at hy
    obtain ⟨n, _, rfl⟩ := hy
    push_cast
    exact neuron_bound M _ _ _ (abs_rW2_le_one p c n) (abs_rE1_le_one p a n) (abs_rE2_le_one p b n)
  · simp only [List.length_map, neurons_length, nsmul_eq_mul]
    push_cast
    ring_nf
    exact le_refl _

/-! ### (iv) Assembly -/

/-- With `24 |S| < M g`, the integer score of every wrong answer is strictly below the right one's. -/
theorem intScore_lt (p : ℕ) (hp : 0 < p) (S : List ℕ) (M : ℕ) (g : ℝ)
    (hg : ∀ s : ℕ, 0 < s → s < p → waveSum p S s ≤ S.length - g)
    (hM : 24 * (S.length : ℝ) < M * g)
    (a b c : ℕ) (hc : c < p) (hne : c ≠ (a + b) % p) :
    intScore p S M a b c < intScore p S M a b ((a + b) % p) := by
  have hR1 : realScore p S a b ((a + b) % p) = 4 * S.length := by
    rw [realScore_eq, waveSum_right p hp]
  have hR2 : realScore p S a b c ≤ 4 * (S.length - g) := by
    rw [realScore_eq]
    linarith [waveSum_wrong p hp S g hg a b c hc hne]
  have hI1 := intScore_close p S M a b ((a + b) % p)
  have hI2 := intScore_close p S M a b c
  rw [abs_le] at hI1 hI2
  have hM0 : (0 : ℝ) < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      simp at hM
      linarith [show (0 : ℝ) ≤ S.length from Nat.cast_nonneg _]
    · exact_mod_cast h
  have hM3 : (0 : ℝ) ≤ (M : ℝ) ^ 3 := by positivity
  have hR2' : (M : ℝ) ^ 3 * realScore p S a b c ≤ (M : ℝ) ^ 3 * (4 * (S.length - g)) :=
    mul_le_mul_of_nonneg_left hR2 hM3
  have hpos : (0 : ℝ) < 4 * (M : ℝ) ^ 2 * (M * g - 24 * S.length) := by
    apply mul_pos (by positivity); linarith
  have e1 : 4 * (M : ℝ) ^ 2 * (M * g - 24 * S.length)
      = 4 * ((M : ℝ) ^ 3 * g) - 96 * ((M : ℝ) ^ 2 * S.length) := by ring
  have e2 : (M : ℝ) ^ 3 * (4 * (S.length - g)) = 4 * ((M : ℝ) ^ 3 * S.length) - 4 * ((M : ℝ) ^ 3 * g) := by
    ring
  have e3 : (M : ℝ) ^ 3 * (4 * (S.length : ℝ)) = 4 * ((M : ℝ) ^ 3 * S.length) := by ring
  have e4 : 48 * (M : ℝ) ^ 2 * S.length = 48 * ((M : ℝ) ^ 2 * S.length) := by ring
  rw [hR1, e3, e4] at hI1
  rw [e4] at hI2
  rw [e2] at hR2'
  rw [e1] at hpos
  have : ((intScore p S M a b c : ℤ) : ℝ) < ((intScore p S M a b ((a + b) % p) : ℤ) : ℝ) := by
    linarith [hI1.1, hI2.2, hR2', hpos]
  exact_mod_cast this

/-- **The theorem.** For every modulus `p ≥ 1`, every list of frequencies `S`, every gap `g` for `S`
(every nonzero shift has wave sum at most `|S| − g`) and every scale `M` with `24 |S| < M g`, the
integer phase-grid network answers `(a + b) % p` on every pair `a, b < p`. -/
theorem adds_mod_p (p : ℕ) (hp : 0 < p) (S : List ℕ) (M : ℕ) (g : ℝ)
    (hg : ∀ s : ℕ, 0 < s → s < p → waveSum p S s ≤ S.length - g)
    (hM : 24 * (S.length : ℝ) < M * g) :
    ∀ a, a < p → ∀ b, b < p → answer p S M a b = (a + b) % p := by
  intro a ha b hb
  unfold answer E1 E2 W2
  rw [LeanCheckedNetwork.answer_ofFn (neurons S) (fun a n => round ((M : ℝ) * rE1 p a n))
    (fun b n => round ((M : ℝ) * rE2 p b n)) (fun c n => round ((M : ℝ) * rW2 p c n)) a b ha hb]
  refine LeanCheckedNetwork.argmax_of_strict _ _ ?_ ?_
  · rw [List.length_ofFn]; exact Nat.mod_lt _ hp
  · intro j hj hne
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact intScore_lt p hp S M g hg hM a b j (by simpa using hj) hne

/-- The same, with the gap `gap p hp S` spelled out as `|S|` minus the largest wave sum. -/
theorem adds_mod_p_of_gap (p : ℕ) (hp : 2 ≤ p) (S : List ℕ) (M : ℕ)
    (hM : 24 * (S.length : ℝ) < M * gap p hp S) :
    ∀ a, a < p → ∀ b, b < p → answer p S M a b = (a + b) % p := by
  apply adds_mod_p p (by omega) S M (gap p hp S) _ hM
  intro s hs hsp
  unfold gap
  have := Finset.le_sup' (fun s : ℕ => waveSum p S s) (show s ∈ Finset.Ico 1 p by simp; omega)
  linarith

end PhaseGrid

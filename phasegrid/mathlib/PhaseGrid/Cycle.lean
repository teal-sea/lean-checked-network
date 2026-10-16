import PhaseGrid.FullSetEven
import PhaseGrid.Close

/-!
# The six-phase cycle network adds mod p

`FIXED_PHASE.md` builds its 12-neuron networks from six neurons per frequency `k`, with phases
`φ₁ = 2πj/6` and `φ₂ = 4φ₁` for `j = 0, …, 5` (`make_fixed_phase6.py`). This file proves the
derivation it states and does not prove.

* `sum_cos_cycle_eq_zero`: for an integer `m` not divisible by `6`,
  `Σ_{j<6} cos(t + m · 2πj/6) = 0` (the six sixth roots of unity `e^{2πi m j/6}` sum to zero).
* `expand_abc`, `expand_phase`: one neuron's term `cos(tc + 5ψ) (cos(ta + ψ) + cos(tb + 4ψ))²` is
  `(1/2) cos(ta + tb − tc)` plus eight waves whose phases are `m ψ` with
  `m ∈ {5, 7, −3, 13, 3, 10, 2, −8}` (the values `u + 4v` of the eight unwanted families).
* `sextet`: summed over the cycle, the eight waves vanish and the six neurons at one frequency
  contribute `3 cos(ta + tb − tc)`.
* `realScoreC_eq`: the real score of the cycle network is `3 Σ_{k∈S} cos(2πk(a + b − c)/p)`.
* `intScoreC_close`: with `6|S|` neurons and `6M²` per neuron (`neuron_bound` from `Score.lean`,
  unchanged), the integer score is within `36 M² |S|` of `M³` times the real score.
* `intScoreC_lt`, `adds_mod_p_cycle`: the margin is `3 M² (M g − 24 |S|)`, so the same hypothesis
  `24 |S| < M g` as for the phase grid makes `answer` return `(a + b) % p` on every pair.
* `adds_mod_p_cycle_tables`: the same for any integer tables within `1/2` of `M cos(…)`.
* `adds_mod_p_cycle_full`: every `p ≥ 3`, all frequencies `1, …, ⌊(p − 1)/2⌋`, every `M ≥ 25`
  (`M ≥ 24` at odd `p`, `adds_mod_p_cycle_full_odd`).

The constant is the same `24` as for the eight-neuron grid: the grid has `8` neurons per frequency,
error `8 · 6M² = 48M²` per frequency and wanted coefficient `4`; the cycle has `6` neurons, error
`36M²` and coefficient `3`; both ratios are `12`, and two scores are compared, hence `24`.
-/

namespace PhaseGrid
open Real

/-- The six phase indices `j = 0, …, 5` of the cycle. -/
def cycle : List ℕ := [0, 1, 2, 3, 4, 5]

/-- The cycle phase `φ₁ = 2πj/6`; `φ₂ = 4 · cyclePhase j`. -/
noncomputable def cyclePhase (j : ℕ) : ℝ := 2 * π * j / 6

/-! ### The cancellation lemma -/

/-- For `m` not divisible by `6`, `Σ_{j<6} cos(t + m · 2πj/6) = 0`: the sum is the real part of
`e^{it} Σ_{j<6} ζ^j` with `ζ = e^{2πi m/6}`, `ζ⁶ = 1`, `ζ ≠ 1`. -/
theorem sum_cos_cycle_eq_zero (t : ℝ) (m : ℤ) (hm : ¬ (6 : ℤ) ∣ m) :
    ∑ j ∈ Finset.range 6, cos (t + (m : ℝ) * cyclePhase j) = 0 := by
  set ζ : ℂ := Complex.exp (((2 * π * m / 6 : ℝ) : ℂ) * Complex.I) with hζ
  have hζ6 : ζ ^ 6 = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    rw [show ((6 : ℕ) : ℂ) * (((2 * π * m / 6 : ℝ) : ℂ) * Complex.I) = (m : ℂ) * (2 * π * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have hζ1 : ζ ≠ 1 := by
    rw [hζ, Ne, Complex.exp_eq_one_iff]
    rintro ⟨n, hn⟩
    have h2 : (2 * π * m / 6 : ℝ) = n * (2 * π) := by
      have := congrArg Complex.im hn
      simpa using this
    have h3 : (m : ℝ) = 6 * n := by
      have hpi : (0 : ℝ) < π := pi_pos
      field_simp at h2
      nlinarith
    have h4 : m = 6 * n := by exact_mod_cast h3
    exact hm ⟨n, h4⟩
  have hsum : ∑ j ∈ Finset.range 6, ζ ^ j = 0 := by
    rw [geom_sum_eq hζ1, hζ6, sub_self, zero_div]
  have hre : ∀ j : ℕ, (Complex.exp ((t : ℂ) * Complex.I) * ζ ^ j).re = cos (t + (m : ℝ) * cyclePhase j) := by
    intro j
    rw [hζ, ← Complex.exp_nat_mul, ← Complex.exp_add,
      show (t : ℂ) * Complex.I + (j : ℂ) * (((2 * π * m / 6 : ℝ) : ℂ) * Complex.I)
        = ((t + (m : ℝ) * cyclePhase j : ℝ) : ℂ) * Complex.I by
        unfold cyclePhase; push_cast; ring]
    exact Complex.exp_ofReal_mul_I_re _
  have h0 : Complex.exp ((t : ℂ) * Complex.I) * ∑ j ∈ Finset.range 6, ζ ^ j = 0 := by
    rw [hsum, mul_zero]
  have := congrArg Complex.re h0
  rw [Finset.mul_sum, Complex.re_sum] at this
  simp only [hre, Complex.zero_re] at this
  exact this

theorem cancel5 (t : ℝ) : ∑ j ∈ Finset.range 6, cos (t + 5 * cyclePhase j) = 0 := by
  have := sum_cos_cycle_eq_zero t 5 (by omega); push_cast at this; exact this
theorem cancel7 (t : ℝ) : ∑ j ∈ Finset.range 6, cos (t + 7 * cyclePhase j) = 0 := by
  have := sum_cos_cycle_eq_zero t 7 (by omega); push_cast at this; exact this
theorem cancel_m3 (t : ℝ) : ∑ j ∈ Finset.range 6, cos (t + (-3) * cyclePhase j) = 0 := by
  have := sum_cos_cycle_eq_zero t (-3) (by omega); push_cast at this; exact this
theorem cancel13 (t : ℝ) : ∑ j ∈ Finset.range 6, cos (t + 13 * cyclePhase j) = 0 := by
  have := sum_cos_cycle_eq_zero t 13 (by omega); push_cast at this; exact this
theorem cancel3 (t : ℝ) : ∑ j ∈ Finset.range 6, cos (t + 3 * cyclePhase j) = 0 := by
  have := sum_cos_cycle_eq_zero t 3 (by omega); push_cast at this; exact this
theorem cancel10 (t : ℝ) : ∑ j ∈ Finset.range 6, cos (t + 10 * cyclePhase j) = 0 := by
  have := sum_cos_cycle_eq_zero t 10 (by omega); push_cast at this; exact this
theorem cancel2 (t : ℝ) : ∑ j ∈ Finset.range 6, cos (t + 2 * cyclePhase j) = 0 := by
  have := sum_cos_cycle_eq_zero t 2 (by omega); push_cast at this; exact this
theorem cancel_m8 (t : ℝ) : ∑ j ∈ Finset.range 6, cos (t + (-8) * cyclePhase j) = 0 := by
  have := sum_cos_cycle_eq_zero t (-8) (by omega); push_cast at this; exact this

/-! ### One neuron is nine waves -/

/-- `cos C (cos A + cos B)²` as nine cosines: the wanted `(1/2) cos(A + B − C)` and eight others. A
polynomial identity in `cos` and `sin` of `A`, `B`, `C` after the addition and double-angle formulas. -/
theorem expand_abc (A B C : ℝ) :
    cos C * (cos A + cos B) ^ 2
      = 1 / 2 * cos (A + B - C) + cos C + 1 / 4 * cos (2 * A + C) + 1 / 4 * cos (2 * A - C)
        + 1 / 4 * cos (2 * B + C) + 1 / 4 * cos (2 * B - C) + 1 / 2 * cos (A + B + C)
        + 1 / 2 * cos (A - B + C) + 1 / 2 * cos (A - B - C) := by
  simp only [cos_add, cos_sub, sin_add, sin_sub, cos_two_mul, sin_two_mul]
  ring

/-- The same with the cycle's phases `φ₁ = ψ`, `φ₂ = 4ψ`: the eight unwanted waves carry `mψ` with
`m = 5, 7, −3, 13, 3, 10, 2, −8` (`u + 4v` for the eight families `(u, v)`). -/
theorem expand_phase (ta tb tc ψ : ℝ) :
    cos (tc + ψ + 4 * ψ) * (cos (ta + ψ) + cos (tb + 4 * ψ)) ^ 2
      = 1 / 2 * cos (ta + tb - tc) + cos (tc + 5 * ψ) + 1 / 4 * cos (2 * ta + tc + 7 * ψ)
        + 1 / 4 * cos (2 * ta - tc + (-3) * ψ) + 1 / 4 * cos (2 * tb + tc + 13 * ψ)
        + 1 / 4 * cos (2 * tb - tc + 3 * ψ) + 1 / 2 * cos (ta + tb + tc + 10 * ψ)
        + 1 / 2 * cos (ta - tb + tc + 2 * ψ) + 1 / 2 * cos (ta - tb - tc + (-8) * ψ) := by
  rw [expand_abc]
  ring_nf

/-- A sum over the list `cycle` is a sum over `Finset.range 6`. -/
theorem cycle_sum (f : ℕ → ℝ) : (cycle.map f).sum = ∑ j ∈ Finset.range 6, f j := by
  simp [cycle, Finset.sum_range_succ, add_assoc]

/-- One sextet of neurons at angles `ta, tb, tc`: the six cycle terms sum to `3 cos(ta + tb − tc)`. -/
theorem sextet (ta tb tc : ℝ) :
    (cycle.map fun j : ℕ => cos (tc + cyclePhase j + 4 * cyclePhase j) *
      (cos (ta + cyclePhase j) + cos (tb + 4 * cyclePhase j)) ^ 2).sum
    = 3 * cos (ta + tb - tc) := by
  rw [cycle_sum, Finset.sum_congr rfl (fun j _ => expand_phase ta tb tc (cyclePhase j))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, cancel5, cancel7, cancel_m3, cancel13,
    cancel3, cancel10, cancel2, cancel_m8, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-! ### The cycle network -/

/-- The neurons for the frequency list `S`: for each `k ∈ S`, the six phases of `cycle`, as pairs
`(k, j)`. -/
def neuronsC (S : List ℕ) : List (ℕ × ℕ) :=
  S.flatMap fun k => cycle.map fun j => (k, j)

theorem neuronsC_cons (k : ℕ) (S : List ℕ) :
    neuronsC (k :: S) = (cycle.map fun j => (k, j)) ++ neuronsC S := rfl

theorem neuronsC_length (S : List ℕ) : (neuronsC S).length = 6 * S.length := by
  induction S with
  | nil => rfl
  | cons k S ih =>
    rw [neuronsC_cons, List.length_append, ih, List.length_map, List.length_cons]
    simp [cycle]; ring

/-- Real weight of neuron `(k, j)` for the first input `a`: `cos(2πka/p + 2πj/6)`. -/
noncomputable def rE1c (p a : ℕ) (n : ℕ × ℕ) : ℝ := cos (θ p n.1 a + cyclePhase n.2)

/-- Real weight of neuron `(k, j)` for the second input `b`: `cos(2πkb/p + 4 · 2πj/6)`. -/
noncomputable def rE2c (p b : ℕ) (n : ℕ × ℕ) : ℝ := cos (θ p n.1 b + 4 * cyclePhase n.2)

/-- Real read-out weight of neuron `(k, j)` for the answer `c`: `cos(2πkc/p + φ₁ + φ₂)`. -/
noncomputable def rW2c (p c : ℕ) (n : ℕ × ℕ) : ℝ :=
  cos (θ p n.1 c + cyclePhase n.2 + 4 * cyclePhase n.2)

/-- The integer embedding table of the first input: row `a` holds `round(M · rE1c p a n)`. -/
noncomputable def E1c (p : ℕ) (S : List ℕ) (M : ℕ) : List (List ℤ) :=
  List.ofFn fun a : Fin p => (neuronsC S).map fun n => round ((M : ℝ) * rE1c p a n)

/-- The integer embedding table of the second input. -/
noncomputable def E2c (p : ℕ) (S : List ℕ) (M : ℕ) : List (List ℤ) :=
  List.ofFn fun b : Fin p => (neuronsC S).map fun n => round ((M : ℝ) * rE2c p b n)

/-- The integer read-out table: row `c` holds the weights of the answer `c`. -/
noncomputable def W2c (p : ℕ) (S : List ℕ) (M : ℕ) : List (List ℤ) :=
  List.ofFn fun c : Fin p => (neuronsC S).map fun n => round ((M : ℝ) * rW2c p c n)

/-- The cycle network's answer for `(a, b)`, computed by the first repository's `answer`. -/
noncomputable def answerC (p : ℕ) (S : List ℕ) (M : ℕ) (a b : ℕ) : ℕ :=
  LeanCheckedNetwork.answer (E1c p S M) (E2c p S M) (W2c p S M) a b

/-- The real score of the answer `c` for the pair `(a, b)`. -/
noncomputable def realScoreC (p : ℕ) (S : List ℕ) (a b c : ℕ) : ℝ :=
  ((neuronsC S).map fun n => rW2c p c n * (rE1c p a n + rE2c p b n) ^ 2).sum

/-- The integer score of the answer `c` for the pair `(a, b)`: what `Network.lean` computes. -/
noncomputable def intScoreC (p : ℕ) (S : List ℕ) (M : ℕ) (a b c : ℕ) : ℤ :=
  ((neuronsC S).map fun n => round ((M : ℝ) * rW2c p c n) *
    ((round ((M : ℝ) * rE1c p a n) + round ((M : ℝ) * rE2c p b n)) *
      (round ((M : ℝ) * rE1c p a n) + round ((M : ℝ) * rE2c p b n)))).sum

/-- The real score of the cycle network is one wave, `3 Σ_{k∈S} cos(2πk(a + b − c)/p)`. -/
theorem realScoreC_eq (p : ℕ) (S : List ℕ) (a b c : ℕ) :
    realScoreC p S a b c = 3 * waveSum p S ((a : ℝ) + b - c) := by
  unfold realScoreC waveSum
  induction S with
  | nil => simp [neuronsC]
  | cons k S ih =>
    rw [neuronsC_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons,
      List.map_map]
    have h := sextet (θ p k a) (θ p k b) (θ p k c)
    rw [show ((fun n => rW2c p c n * (rE1c p a n + rE2c p b n) ^ 2) ∘ fun j : ℕ => (k, j))
        = fun j : ℕ => cos (θ p k c + cyclePhase j + 4 * cyclePhase j) *
          (cos (θ p k a + cyclePhase j) + cos (θ p k b + 4 * cyclePhase j)) ^ 2 from rfl, h]
    rw [show θ p k a + θ p k b - θ p k c = 2 * π * k * ((a : ℝ) + b - c) / p by unfold θ; ring]
    ring

theorem abs_rE1c_le_one (p a : ℕ) (n : ℕ × ℕ) : |rE1c p a n| ≤ 1 := abs_cos_le_one _
theorem abs_rE2c_le_one (p b : ℕ) (n : ℕ × ℕ) : |rE2c p b n| ≤ 1 := abs_cos_le_one _
theorem abs_rW2c_le_one (p c : ℕ) (n : ℕ × ℕ) : |rW2c p c n| ≤ 1 := abs_cos_le_one _

/-- The integer score is within `36 M² |S|` of `M³` times the real score (`6|S|` neurons, `6M²` each,
by `neuron_bound`). -/
theorem intScoreC_close (p : ℕ) (S : List ℕ) (M : ℕ) (a b c : ℕ) :
    |((intScoreC p S M a b c : ℤ) : ℝ) - (M : ℝ) ^ 3 * realScoreC p S a b c|
      ≤ 36 * (M : ℝ) ^ 2 * S.length := by
  unfold intScoreC realScoreC
  rw [Int.cast_list_sum, List.map_map, list_sum_mul_left, list_sum_sub]
  refine (abs_list_sum_le _).trans ?_
  refine (List.sum_le_length_nsmul _ (6 * (M : ℝ) ^ 2) ?_).trans ?_
  · intro y hy
    simp only [List.map_map, List.mem_map, Function.comp] at hy
    obtain ⟨n, _, rfl⟩ := hy
    push_cast
    exact neuron_bound M _ _ _ (abs_rW2c_le_one p c n) (abs_rE1c_le_one p a n) (abs_rE2c_le_one p b n)
  · simp only [List.length_map, neuronsC_length, nsmul_eq_mul]
    push_cast
    ring_nf
    exact le_refl _

/-- With `24 |S| < M g`, every wrong answer's integer score is strictly below the right one's: the
margin is at least `3 M² (M g − 24 |S|)`. -/
theorem intScoreC_lt (p : ℕ) (hp : 0 < p) (S : List ℕ) (M : ℕ) (g : ℝ)
    (hg : ∀ s : ℕ, 0 < s → s < p → waveSum p S s ≤ S.length - g)
    (hM : 24 * (S.length : ℝ) < M * g)
    (a b c : ℕ) (hc : c < p) (hne : c ≠ (a + b) % p) :
    intScoreC p S M a b c < intScoreC p S M a b ((a + b) % p) := by
  have hR1 : realScoreC p S a b ((a + b) % p) = 3 * S.length := by
    rw [realScoreC_eq, waveSum_right p hp]
  have hR2 : realScoreC p S a b c ≤ 3 * (S.length - g) := by
    rw [realScoreC_eq]
    linarith [waveSum_wrong p hp S g hg a b c hc hne]
  have hI1 := intScoreC_close p S M a b ((a + b) % p)
  have hI2 := intScoreC_close p S M a b c
  rw [abs_le] at hI1 hI2
  have hM0 : (0 : ℝ) < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      simp at hM
      linarith [show (0 : ℝ) ≤ S.length from Nat.cast_nonneg _]
    · exact_mod_cast h
  have hM3 : (0 : ℝ) ≤ (M : ℝ) ^ 3 := by positivity
  have hR2' : (M : ℝ) ^ 3 * realScoreC p S a b c ≤ (M : ℝ) ^ 3 * (3 * (S.length - g)) :=
    mul_le_mul_of_nonneg_left hR2 hM3
  have hpos : (0 : ℝ) < 3 * (M : ℝ) ^ 2 * (M * g - 24 * S.length) := by
    apply mul_pos (by positivity); linarith
  have e1 : 3 * (M : ℝ) ^ 2 * (M * g - 24 * S.length)
      = 3 * ((M : ℝ) ^ 3 * g) - 72 * ((M : ℝ) ^ 2 * S.length) := by ring
  have e2 : (M : ℝ) ^ 3 * (3 * (S.length - g)) = 3 * ((M : ℝ) ^ 3 * S.length) - 3 * ((M : ℝ) ^ 3 * g) := by
    ring
  have e3 : (M : ℝ) ^ 3 * (3 * (S.length : ℝ)) = 3 * ((M : ℝ) ^ 3 * S.length) := by ring
  have e4 : 36 * (M : ℝ) ^ 2 * S.length = 36 * ((M : ℝ) ^ 2 * S.length) := by ring
  rw [hR1, e3, e4] at hI1
  rw [e4] at hI2
  rw [e2] at hR2'
  rw [e1] at hpos
  have : ((intScoreC p S M a b c : ℤ) : ℝ) < ((intScoreC p S M a b ((a + b) % p) : ℤ) : ℝ) := by
    linarith [hI1.1, hI2.2, hR2', hpos]
  exact_mod_cast this

/-- **The theorem for the cycle.** For every modulus `p ≥ 1`, every list of frequencies `S`, every
gap `g` for `S` (every nonzero shift has wave sum at most `|S| − g`) and every scale `M` with
`24 |S| < M g`, the integer six-phase cycle network answers `(a + b) % p` on every pair `a, b < p`. -/
theorem adds_mod_p_cycle (p : ℕ) (hp : 0 < p) (S : List ℕ) (M : ℕ) (g : ℝ)
    (hg : ∀ s : ℕ, 0 < s → s < p → waveSum p S s ≤ S.length - g)
    (hM : 24 * (S.length : ℝ) < M * g) :
    ∀ a, a < p → ∀ b, b < p → answerC p S M a b = (a + b) % p := by
  intro a ha b hb
  unfold answerC E1c E2c W2c
  rw [LeanCheckedNetwork.answer_ofFn (neuronsC S) (fun a n => round ((M : ℝ) * rE1c p a n))
    (fun b n => round ((M : ℝ) * rE2c p b n)) (fun c n => round ((M : ℝ) * rW2c p c n)) a b ha hb]
  refine LeanCheckedNetwork.argmax_of_strict _ _ ?_ ?_
  · rw [List.length_ofFn]; exact Nat.mod_lt _ hp
  · intro j hj hne
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact intScoreC_lt p hp S M g hg hM a b j (by simpa using hj) hne

/-- The same, with the gap `gap p hp S` spelled out as `|S|` minus the largest wave sum. -/
theorem adds_mod_p_cycle_of_gap (p : ℕ) (hp : 2 ≤ p) (S : List ℕ) (M : ℕ)
    (hM : 24 * (S.length : ℝ) < M * gap p hp S) :
    ∀ a, a < p → ∀ b, b < p → answerC p S M a b = (a + b) % p := by
  apply adds_mod_p_cycle p (by omega) S M (gap p hp S) _ hM
  intro s hs hsp
  unfold gap
  have := Finset.le_sup' (fun s : ℕ => waveSum p S s) (show s ∈ Finset.Ico 1 p by simp; omega)
  linarith

/-! ### Any tables within 1/2 of the cycle weights -/

/-- The integer score computed by `Network.lean` from arbitrary tables over the cycle neurons. -/
noncomputable def intScoreCT (S : List ℕ) (t1 t2 tw : ℕ → ℕ × ℕ → ℤ) (a b c : ℕ) : ℤ :=
  ((neuronsC S).map fun n => tw c n * ((t1 a n + t2 b n) * (t1 a n + t2 b n))).sum

theorem intScoreCT_close (p : ℕ) (S : List ℕ) (M : ℕ) (t1 t2 tw : ℕ → ℕ × ℕ → ℤ)
    (h1 : ∀ a, a < p → ∀ n ∈ neuronsC S, |(t1 a n : ℝ) - M * rE1c p a n| ≤ 1 / 2)
    (h2 : ∀ b, b < p → ∀ n ∈ neuronsC S, |(t2 b n : ℝ) - M * rE2c p b n| ≤ 1 / 2)
    (hw : ∀ c, c < p → ∀ n ∈ neuronsC S, |(tw c n : ℝ) - M * rW2c p c n| ≤ 1 / 2)
    (a b c : ℕ) (ha : a < p) (hb : b < p) (hc : c < p) :
    |((intScoreCT S t1 t2 tw a b c : ℤ) : ℝ) - (M : ℝ) ^ 3 * realScoreC p S a b c|
      ≤ 36 * (M : ℝ) ^ 2 * S.length := by
  unfold intScoreCT realScoreC
  rw [Int.cast_list_sum, List.map_map, list_sum_mul_left, list_sum_sub]
  refine (abs_list_sum_le _).trans ?_
  refine (List.sum_le_length_nsmul _ (6 * (M : ℝ) ^ 2) ?_).trans ?_
  · intro y hy
    simp only [List.map_map, List.mem_map, Function.comp] at hy
    obtain ⟨n, hn, rfl⟩ := hy
    push_cast
    exact neuron_bound_close M _ _ _ _ _ _ (abs_rW2c_le_one p c n) (abs_rE1c_le_one p a n)
      (abs_rE2c_le_one p b n) (hw c hc n hn) (h1 a ha n hn) (h2 b hb n hn)
  · simp only [List.length_map, neuronsC_length, nsmul_eq_mul]
    push_cast
    ring_nf
    exact le_refl _

theorem intScoreCT_lt (p : ℕ) (hp : 0 < p) (S : List ℕ) (M : ℕ) (g : ℝ)
    (hg : ∀ s : ℕ, 0 < s → s < p → waveSum p S s ≤ S.length - g)
    (hM : 24 * (S.length : ℝ) < M * g)
    (t1 t2 tw : ℕ → ℕ × ℕ → ℤ)
    (h1 : ∀ a, a < p → ∀ n ∈ neuronsC S, |(t1 a n : ℝ) - M * rE1c p a n| ≤ 1 / 2)
    (h2 : ∀ b, b < p → ∀ n ∈ neuronsC S, |(t2 b n : ℝ) - M * rE2c p b n| ≤ 1 / 2)
    (hw : ∀ c, c < p → ∀ n ∈ neuronsC S, |(tw c n : ℝ) - M * rW2c p c n| ≤ 1 / 2)
    (a b c : ℕ) (ha : a < p) (hb : b < p) (hc : c < p) (hne : c ≠ (a + b) % p) :
    intScoreCT S t1 t2 tw a b c < intScoreCT S t1 t2 tw a b ((a + b) % p) := by
  have hR1 : realScoreC p S a b ((a + b) % p) = 3 * S.length := by
    rw [realScoreC_eq, waveSum_right p hp]
  have hR2 : realScoreC p S a b c ≤ 3 * (S.length - g) := by
    rw [realScoreC_eq]
    linarith [waveSum_wrong p hp S g hg a b c hc hne]
  have hI1 := intScoreCT_close p S M t1 t2 tw h1 h2 hw a b ((a + b) % p) ha hb (Nat.mod_lt _ hp)
  have hI2 := intScoreCT_close p S M t1 t2 tw h1 h2 hw a b c ha hb hc
  rw [abs_le] at hI1 hI2
  have hM0 : (0 : ℝ) < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      simp at hM
      linarith [show (0 : ℝ) ≤ S.length from Nat.cast_nonneg _]
    · exact_mod_cast h
  have hM3 : (0 : ℝ) ≤ (M : ℝ) ^ 3 := by positivity
  have hR2' : (M : ℝ) ^ 3 * realScoreC p S a b c ≤ (M : ℝ) ^ 3 * (3 * (S.length - g)) :=
    mul_le_mul_of_nonneg_left hR2 hM3
  have hpos : (0 : ℝ) < 3 * (M : ℝ) ^ 2 * (M * g - 24 * S.length) := by
    apply mul_pos (by positivity); linarith
  have e1 : 3 * (M : ℝ) ^ 2 * (M * g - 24 * S.length)
      = 3 * ((M : ℝ) ^ 3 * g) - 72 * ((M : ℝ) ^ 2 * S.length) := by ring
  have e2 : (M : ℝ) ^ 3 * (3 * (S.length - g)) = 3 * ((M : ℝ) ^ 3 * S.length) - 3 * ((M : ℝ) ^ 3 * g) := by
    ring
  have e3 : (M : ℝ) ^ 3 * (3 * (S.length : ℝ)) = 3 * ((M : ℝ) ^ 3 * S.length) := by ring
  have e4 : 36 * (M : ℝ) ^ 2 * S.length = 36 * ((M : ℝ) ^ 2 * S.length) := by ring
  rw [hR1, e3, e4] at hI1
  rw [e4] at hI2
  rw [e2] at hR2'
  rw [e1] at hpos
  have : ((intScoreCT S t1 t2 tw a b c : ℤ) : ℝ) < ((intScoreCT S t1 t2 tw a b ((a + b) % p) : ℤ) : ℝ) := by
    linarith [hI1.1, hI2.2, hR2', hpos]
  exact_mod_cast this

/-- **Any close tables over the cycle neurons.** Integer tables whose entries (rows `< p`, neurons of
`S`) are within `1/2` of `M` times the cycle weights make `LeanCheckedNetwork.answer` return
`(a + b) % p` on every pair, under the same gap and scale hypotheses. This is the statement that an
explicit network such as `FixedPhase12` would be linked to, once its entries are certified. -/
theorem adds_mod_p_cycle_tables (p : ℕ) (hp : 0 < p) (S : List ℕ) (M : ℕ) (g : ℝ)
    (hg : ∀ s : ℕ, 0 < s → s < p → waveSum p S s ≤ S.length - g)
    (hM : 24 * (S.length : ℝ) < M * g)
    (t1 t2 tw : ℕ → ℕ × ℕ → ℤ)
    (h1 : ∀ a, a < p → ∀ n ∈ neuronsC S, |(t1 a n : ℝ) - M * rE1c p a n| ≤ 1 / 2)
    (h2 : ∀ b, b < p → ∀ n ∈ neuronsC S, |(t2 b n : ℝ) - M * rE2c p b n| ≤ 1 / 2)
    (hw : ∀ c, c < p → ∀ n ∈ neuronsC S, |(tw c n : ℝ) - M * rW2c p c n| ≤ 1 / 2) :
    ∀ a, a < p → ∀ b, b < p →
      LeanCheckedNetwork.answer (List.ofFn fun a : Fin p => (neuronsC S).map (t1 a))
        (List.ofFn fun b : Fin p => (neuronsC S).map (t2 b))
        (List.ofFn fun c : Fin p => (neuronsC S).map (tw c)) a b = (a + b) % p := by
  intro a ha b hb
  rw [LeanCheckedNetwork.answer_ofFn (neuronsC S) t1 t2 tw a b ha hb]
  refine LeanCheckedNetwork.argmax_of_strict _ _ ?_ ?_
  · rw [List.length_ofFn]; exact Nat.mod_lt _ hp
  · intro j hj hne
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact intScoreCT_lt p hp S M g hg hM t1 t2 tw h1 h2 hw a b j ha hb (by simpa using hj) hne

/-! ### All frequencies -/

/-- **Every odd modulus.** For `p = 2m + 1 ≥ 3`, the frequencies `1, …, m` and any scale `M ≥ 24`,
the integer cycle network adds mod `p` on every pair (gap `p/2`, by `waveSum_full_odd`). -/
theorem adds_mod_p_cycle_full_odd (m : ℕ) (hm : 1 ≤ m) (M : ℕ) (hM : 24 ≤ M) :
    ∀ a, a < 2 * m + 1 → ∀ b, b < 2 * m + 1 →
      answerC (2 * m + 1) (List.range' 1 m) M a b = (a + b) % (2 * m + 1) := by
  apply adds_mod_p_cycle (2 * m + 1) (by omega) (List.range' 1 m) M (((2 * m + 1 : ℕ) : ℝ) / 2)
  · intro s hs0 hsp
    rw [waveSum_full_odd m s hs0 hsp, List.length_range']
    push_cast; linarith
  · rw [List.length_range']
    have h24 : (24 : ℝ) ≤ M := by exact_mod_cast hM
    have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    nlinarith

/-- **Every even modulus.** For `p = 2m ≥ 4`, the frequencies `1, …, m − 1` and any scale `M ≥ 25`
(gap `|S|`, by `waveSum_full_even`; the bound is then exactly `24`, so `25` is needed). -/
theorem adds_mod_p_cycle_full_even (m : ℕ) (hm : 2 ≤ m) (M : ℕ) (hM : 25 ≤ M) :
    ∀ a, a < 2 * m → ∀ b, b < 2 * m →
      answerC (2 * m) (List.range' 1 (m - 1)) M a b = (a + b) % (2 * m) := by
  apply adds_mod_p_cycle (2 * m) (by omega) (List.range' 1 (m - 1)) M ((m - 1 : ℕ) : ℝ)
  · intro s hs0 hsp
    rw [List.length_range']
    have := waveSum_full_even m s (by omega) hs0 hsp
    linarith
  · rw [List.length_range']
    have h25 : (25 : ℝ) ≤ M := by exact_mod_cast hM
    have hm' : (1 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m - 1 by omega)
    nlinarith

/-- **Every modulus `p ≥ 3`**, all frequencies `1, …, ⌊(p − 1)/2⌋`, every scale `M ≥ 25`: the integer
six-phase cycle network answers `(a + b) % p` on every pair `a, b < p`. The constant is the same as
for the eight-phase grid (`adds_mod_p_full`), for the reason given at the top of this file. -/
theorem adds_mod_p_cycle_full (p : ℕ) (hp : 3 ≤ p) (M : ℕ) (hM : 25 ≤ M) :
    ∀ a, a < p → ∀ b, b < p → answerC p (List.range' 1 ((p - 1) / 2)) M a b = (a + b) % p := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' p
  · subst hm
    rw [show (2 * m - 1) / 2 = m - 1 by omega]
    exact adds_mod_p_cycle_full_even m (by omega) M hM
  · subst hm
    rw [show (2 * m + 1 - 1) / 2 = m by omega]
    exact adds_mod_p_cycle_full_odd m (by omega) M (by omega)

/-- The two moduli of `FIXED_PHASE.md`'s 12-neuron networks, with all frequencies: `p = 113`
(`S = 1..56`, 336 neurons) and `p = 257` (`S = 1..128`, 768 neurons), every `M ≥ 24`. -/
theorem adds_mod_113_cycle_full (M : ℕ) (hM : 24 ≤ M) :
    ∀ a, a < 113 → ∀ b, b < 113 → answerC 113 (List.range' 1 56) M a b = (a + b) % 113 :=
  adds_mod_p_cycle_full_odd 56 (by norm_num) M hM

theorem adds_mod_257_cycle_full (M : ℕ) (hM : 24 ≤ M) :
    ∀ a, a < 257 → ∀ b, b < 257 → answerC 257 (List.range' 1 128) M a b = (a + b) % 257 :=
  adds_mod_p_cycle_full_odd 128 (by norm_num) M hM

end PhaseGrid

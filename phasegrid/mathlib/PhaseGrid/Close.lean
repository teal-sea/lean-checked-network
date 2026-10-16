import PhaseGrid.Score

/-!
# Any integer tables within 1/2 of the analytic weights add mod p

`Score.lean` proves the theorem for the tables `round(M · cos(…))`. The only property of `round` that
proof uses is `|round(M w) − M w| ≤ 1/2`. This file states the theorem for arbitrary integer tables
`t1 t2 tw : ℕ → neuron → ℤ` whose entries (rows `< p`, neurons of `S`) are within `1/2` of `M` times
the analytic weights (`adds_mod_p_tables`), and recovers the `round` version from it (`adds_mod_p_of_close_round`).
The point: a table produced by any rounding convention, or by floating-point arithmetic, is covered
as soon as each entry is certified to lie within `1/2` of `M cos(…)`; nothing about how it was
computed enters the theorem.
-/

namespace PhaseGrid
open Real

/-- An integer within `1/2` of `M e` with `|e| ≤ 1` has absolute value at most `M`. -/
theorem abs_int_le_of_close (M : ℕ) (e : ℝ) (x : ℤ) (he : |e| ≤ 1)
    (hx : |(x : ℝ) - M * e| ≤ 1 / 2) : |(x : ℝ)| ≤ M := by
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hMe : |(M : ℝ) * e| ≤ M := by
    rw [abs_mul, abs_of_nonneg hM]
    calc (M : ℝ) * |e| ≤ M * 1 := mul_le_mul_of_nonneg_left he hM
      _ = M := mul_one _
  have h2 : |(x : ℝ)| ≤ M + 1 / 2 := by
    calc |(x : ℝ)| = |(M : ℝ) * e + ((x : ℝ) - M * e)| := by congr 1; ring
      _ ≤ |(M : ℝ) * e| + |(x : ℝ) - M * e| := abs_add_le _ _
      _ ≤ M + 1 / 2 := add_le_add hMe hx
  rw [abs_le] at h2 ⊢
  obtain ⟨h2l, h2r⟩ := h2
  constructor
  · have : (-(M : ℤ) - 1 : ℤ) < x := by
      have : ((-(M : ℤ) - 1 : ℤ) : ℝ) < (x : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have : -(M : ℤ) ≤ x := by omega
    exact_mod_cast this
  · have : x < (M : ℤ) + 1 := by
      have : (x : ℝ) < (((M : ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have : x ≤ (M : ℤ) := by omega
    exact_mod_cast this

/-- One neuron, for arbitrary integers `w' x1 x2` within `1/2` of `M w`, `M e1`, `M e2`:
`w' (x1 + x2)²` is within `6 M²` of `M³ w (e1 + e2)²`. -/
theorem neuron_bound_close (M : ℕ) (w e1 e2 : ℝ) (w' x1 x2 : ℤ)
    (hw : |w| ≤ 1) (h1 : |e1| ≤ 1) (h2 : |e2| ≤ 1)
    (hw' : |(w' : ℝ) - M * w| ≤ 1 / 2) (hx1 : |(x1 : ℝ) - M * e1| ≤ 1 / 2)
    (hx2 : |(x2 : ℝ) - M * e2| ≤ 1 / 2) :
    |(w' : ℝ) * (((x1 : ℝ) + x2) * ((x1 : ℝ) + x2)) - (M : ℝ) ^ 3 * (w * (e1 + e2) ^ 2)|
      ≤ 6 * (M : ℝ) ^ 2 := by
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hx : |(x1 : ℝ) + x2| ≤ 2 * M := by
    calc _ ≤ |(x1 : ℝ)| + |(x2 : ℝ)| := abs_add_le _ _
      _ ≤ M + M := add_le_add (abs_int_le_of_close M e1 x1 h1 hx1) (abs_int_le_of_close M e2 x2 h2 hx2)
      _ = 2 * M := by ring
  have hX : |(M : ℝ) * e1 + M * e2| ≤ 2 * M := by
    calc _ ≤ |(M : ℝ) * e1| + |(M : ℝ) * e2| := abs_add_le _ _
      _ ≤ M * 1 + M * 1 := by
        apply add_le_add
        · rw [abs_mul, abs_of_nonneg hM]; exact mul_le_mul_of_nonneg_left h1 hM
        · rw [abs_mul, abs_of_nonneg hM]; exact mul_le_mul_of_nonneg_left h2 hM
      _ = 2 * M := by ring
  have hxX : |((x1 : ℝ) + x2) - ((M : ℝ) * e1 + M * e2)| ≤ 1 := by
    calc _ = |((x1 : ℝ) - M * e1) + ((x2 : ℝ) - M * e2)| := by congr 1; ring
      _ ≤ |(x1 : ℝ) - M * e1| + |(x2 : ℝ) - M * e2| := abs_add_le _ _
      _ ≤ 1 / 2 + 1 / 2 := add_le_add hx1 hx2
      _ = 1 := by norm_num
  have hxpX : |((x1 : ℝ) + x2) + ((M : ℝ) * e1 + M * e2)| ≤ 4 * M := by
    calc _ ≤ |(x1 : ℝ) + x2| + |(M : ℝ) * e1 + M * e2| := abs_add_le _ _
      _ ≤ 2 * M + 2 * M := add_le_add hx hX
      _ = 4 * M := by ring
  have hMw : |(M : ℝ) * w| ≤ M := by
    rw [abs_mul, abs_of_nonneg hM]
    calc (M : ℝ) * |w| ≤ M * 1 := mul_le_mul_of_nonneg_left hw hM
      _ = M := mul_one _
  set x : ℝ := (x1 : ℝ) + x2 with hxdef
  set X : ℝ := (M : ℝ) * e1 + M * e2 with hXdef
  have key : (w' : ℝ) * (x * x) - (M : ℝ) ^ 3 * (w * (e1 + e2) ^ 2)
      = ((w' : ℝ) - M * w) * (x * x) + (M * w) * ((x - X) * (x + X)) := by
    rw [hXdef]; ring
  rw [key]
  calc |((w' : ℝ) - M * w) * (x * x) + (M * w) * ((x - X) * (x + X))|
      ≤ |((w' : ℝ) - M * w) * (x * x)| + |(M * w) * ((x - X) * (x + X))| := abs_add_le _ _
    _ ≤ 1 / 2 * ((2 * M) * (2 * M)) + M * (1 * (4 * M)) := by
        apply add_le_add
        · rw [abs_mul, abs_mul]
          exact mul_le_mul hw' (mul_le_mul hx hx (abs_nonneg _) (by positivity)) (by positivity)
            (by norm_num)
        · rw [abs_mul]
          exact mul_le_mul hMw (by rw [abs_mul]; exact mul_le_mul hxX hxpX (abs_nonneg _) (by positivity))
            (abs_nonneg _) hM
    _ = 6 * (M : ℝ) ^ 2 := by ring

/-- The integer score computed by `Network.lean` from arbitrary tables `t1 t2 tw`
(entry of neuron `n` in row `x`). -/
noncomputable def intScoreT (S : List ℕ) (t1 t2 tw : ℕ → ℕ × ℕ × ℕ → ℤ) (a b c : ℕ) : ℤ :=
  ((neurons S).map fun n => tw c n * ((t1 a n + t2 b n) * (t1 a n + t2 b n))).sum

/-- Tables within `1/2` of `M` times the analytic weights: the integer score is within `48 M² |S|`
of `M³` times the real score. -/
theorem intScoreT_close (p : ℕ) (S : List ℕ) (M : ℕ) (t1 t2 tw : ℕ → ℕ × ℕ × ℕ → ℤ)
    (h1 : ∀ a, a < p → ∀ n ∈ neurons S, |(t1 a n : ℝ) - M * rE1 p a n| ≤ 1 / 2)
    (h2 : ∀ b, b < p → ∀ n ∈ neurons S, |(t2 b n : ℝ) - M * rE2 p b n| ≤ 1 / 2)
    (hw : ∀ c, c < p → ∀ n ∈ neurons S, |(tw c n : ℝ) - M * rW2 p c n| ≤ 1 / 2)
    (a b c : ℕ) (ha : a < p) (hb : b < p) (hc : c < p) :
    |((intScoreT S t1 t2 tw a b c : ℤ) : ℝ) - (M : ℝ) ^ 3 * realScore p S a b c|
      ≤ 48 * (M : ℝ) ^ 2 * S.length := by
  unfold intScoreT realScore
  rw [Int.cast_list_sum, List.map_map, list_sum_mul_left, list_sum_sub]
  refine (abs_list_sum_le _).trans ?_
  refine (List.sum_le_length_nsmul _ (6 * (M : ℝ) ^ 2) ?_).trans ?_
  · intro y hy
    simp only [List.map_map, List.mem_map, Function.comp] at hy
    obtain ⟨n, hn, rfl⟩ := hy
    push_cast
    exact neuron_bound_close M _ _ _ _ _ _ (abs_rW2_le_one p c n) (abs_rE1_le_one p a n)
      (abs_rE2_le_one p b n) (hw c hc n hn) (h1 a ha n hn) (h2 b hb n hn)
  · simp only [List.length_map, neurons_length, nsmul_eq_mul]
    push_cast
    ring_nf
    exact le_refl _

/-- With `24 |S| < M g`, every wrong answer's integer score is strictly below the right one's. -/
theorem intScoreT_lt (p : ℕ) (hp : 0 < p) (S : List ℕ) (M : ℕ) (g : ℝ)
    (hg : ∀ s : ℕ, 0 < s → s < p → waveSum p S s ≤ S.length - g)
    (hM : 24 * (S.length : ℝ) < M * g)
    (t1 t2 tw : ℕ → ℕ × ℕ × ℕ → ℤ)
    (h1 : ∀ a, a < p → ∀ n ∈ neurons S, |(t1 a n : ℝ) - M * rE1 p a n| ≤ 1 / 2)
    (h2 : ∀ b, b < p → ∀ n ∈ neurons S, |(t2 b n : ℝ) - M * rE2 p b n| ≤ 1 / 2)
    (hw : ∀ c, c < p → ∀ n ∈ neurons S, |(tw c n : ℝ) - M * rW2 p c n| ≤ 1 / 2)
    (a b c : ℕ) (ha : a < p) (hb : b < p) (hc : c < p) (hne : c ≠ (a + b) % p) :
    intScoreT S t1 t2 tw a b c < intScoreT S t1 t2 tw a b ((a + b) % p) := by
  have hR1 : realScore p S a b ((a + b) % p) = 4 * S.length := by
    rw [realScore_eq, waveSum_right p hp]
  have hR2 : realScore p S a b c ≤ 4 * (S.length - g) := by
    rw [realScore_eq]
    linarith [waveSum_wrong p hp S g hg a b c hc hne]
  have hI1 := intScoreT_close p S M t1 t2 tw h1 h2 hw a b ((a + b) % p) ha hb (Nat.mod_lt _ hp)
  have hI2 := intScoreT_close p S M t1 t2 tw h1 h2 hw a b c ha hb hc
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
  have : ((intScoreT S t1 t2 tw a b c : ℤ) : ℝ) < ((intScoreT S t1 t2 tw a b ((a + b) % p) : ℤ) : ℝ) := by
    linarith [hI1.1, hI2.2, hR2', hpos]
  exact_mod_cast this

/-- **The theorem for arbitrary close tables.** For every modulus `p ≥ 1`, every list of frequencies
`S`, every gap `g` for `S` and every scale `M` with `24 |S| < M g`: any integer tables whose entries are
within `1/2` of `M` times the analytic weights make `LeanCheckedNetwork.answer` return `(a + b) % p`
on every pair `a, b < p`. -/
theorem adds_mod_p_tables (p : ℕ) (hp : 0 < p) (S : List ℕ) (M : ℕ) (g : ℝ)
    (hg : ∀ s : ℕ, 0 < s → s < p → waveSum p S s ≤ S.length - g)
    (hM : 24 * (S.length : ℝ) < M * g)
    (t1 t2 tw : ℕ → ℕ × ℕ × ℕ → ℤ)
    (h1 : ∀ a, a < p → ∀ n ∈ neurons S, |(t1 a n : ℝ) - M * rE1 p a n| ≤ 1 / 2)
    (h2 : ∀ b, b < p → ∀ n ∈ neurons S, |(t2 b n : ℝ) - M * rE2 p b n| ≤ 1 / 2)
    (hw : ∀ c, c < p → ∀ n ∈ neurons S, |(tw c n : ℝ) - M * rW2 p c n| ≤ 1 / 2) :
    ∀ a, a < p → ∀ b, b < p →
      LeanCheckedNetwork.answer (List.ofFn fun a : Fin p => (neurons S).map (t1 a))
        (List.ofFn fun b : Fin p => (neurons S).map (t2 b))
        (List.ofFn fun c : Fin p => (neurons S).map (tw c)) a b = (a + b) % p := by
  intro a ha b hb
  rw [LeanCheckedNetwork.answer_ofFn (neurons S) t1 t2 tw a b ha hb]
  refine LeanCheckedNetwork.argmax_of_strict _ _ ?_ ?_
  · rw [List.length_ofFn]; exact Nat.mod_lt _ hp
  · intro j hj hne
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact intScoreT_lt p hp S M g hg hM t1 t2 tw h1 h2 hw a b j ha hb (by simpa using hj) hne

/-- The `round` tables are close tables, so `Score.lean`'s `adds_mod_p` is a corollary. -/
theorem adds_mod_p_of_close_round (p : ℕ) (hp : 0 < p) (S : List ℕ) (M : ℕ) (g : ℝ)
    (hg : ∀ s : ℕ, 0 < s → s < p → waveSum p S s ≤ S.length - g)
    (hM : 24 * (S.length : ℝ) < M * g) :
    ∀ a, a < p → ∀ b, b < p → answer p S M a b = (a + b) % p := by
  unfold answer E1 E2 W2
  exact adds_mod_p_tables p hp S M g hg hM _ _ _
    (fun a _ n _ => by rw [abs_sub_comm]; exact abs_sub_round _)
    (fun b _ n _ => by rw [abs_sub_comm]; exact abs_sub_round _)
    (fun c _ n _ => by rw [abs_sub_comm]; exact abs_sub_round _)

end PhaseGrid

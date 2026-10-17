import Transformer.Compose

namespace Transformer

theorem real_model_adds_mod_113_pointwise
    (p : ExpParams) (hn : 0 < p.n) (hm : 0 < p.m) (hR : p.R ≤ 2 ^ p.m)
    (hclamp : (2 : ℝ) ^ p.f ≤ Real.exp p.R)
    (δ : ℕ) (hδ : deltaBound p ≤ δ)
    (T : Tables) (B : Bounds) (hB : T.Bounded B) (S : ℕ) (hS : 0 < S)
    (a b : Fin 113)
    (hA : ∀ k, k ≠ ans a b →
      intLogits p T S a b k + 2 * (Ebound S p.f δ B : ℤ) < intLogits p T S a b (ans a b)) :
    (∀ k, k ≠ ans a b → mq T S p.t a b k < mq T S p.t a b (ans a b)) ∧
        argmaxFirst (mq T S p.t a b) = ans a b := by
  set tok := toks a b with htok
  -- the twelve integer weights, cast to the reals, and the twelve real weights
  set e : Fin 4 → Fin 3 → ℝ := fun h j => ((eInt p T tok h j : ℤ) : ℝ) with he_def
  set e' : Fin 4 → Fin 3 → ℝ := eReal p T tok with he'_def
  have hMe : (Me p.f δ : ℝ) = 2 ^ p.f + δ := by simp [Me]
  have he : ∀ h j, |e h j| ≤ Me p.f δ := by
    intro h j
    have h0 : (0 : ℝ) ≤ e h j := by simp [he_def, eInt]
    rw [abs_of_nonneg h0, hMe]
    have := expFix_le p hn hm hR hclamp _ (shifted_nonpos T tok h j)
    simp only [he_def, eInt, Int.cast_natCast]
    linarith
  have he' : ∀ h j, |e' h j| ≤ Me p.f δ := by
    intro h j
    have hb := realExp_bounds p (shifted T tok h j) (shifted_nonpos T tok h j)
    simp only [he'_def, eReal]
    rw [abs_of_nonneg hb.1, hMe]
    have : (0 : ℝ) ≤ δ := by positivity
    linarith [hb.2]
  have hd : ∀ h j, |e h j - e' h j| ≤ δ := by
    intro h j
    have := expFix_close p hn hm hR hclamp _ (shifted_nonpos T tok h j)
    simp only [he_def, he'_def, eInt, eReal, Int.cast_natCast]
    linarith
  have hclose : ∀ k, |((intLogits p T S a b k : ℤ) : ℝ) - realExpLogits p T S a b k| ≤
      Ebound S p.f δ B := by
    intro k
    unfold intLogits realExpLogits
    rw [logits_cast]
    exact logits_close T B hB S p.f δ tok e e' he he' hd k
  have hstrict := strict_max_of_margin (intLogits p T S a b) (realExpLogits p T S a b)
    (Ebound S p.f δ B) (ans a b) hA hclose
  have hpos : 0 < Dprod (eReal p T tok) * (S : ℝ) ^ 6 := by
    have := Dprod_eReal_pos p T tok
    positivity
  have hmq : ∀ k, k ≠ ans a b → mq T S p.t a b k < mq T S p.t a b (ans a b) := by
    intro k hk
    have h := hstrict k hk
    unfold realExpLogits at h
    rw [realExp_eq_mq p T tok S hS, realExp_eq_mq p T tok S hS] at h
    unfold mq
    exact lt_of_mul_lt_mul_left h hpos.le
  exact ⟨hmq, argmaxFirst_eq _ _ hmq⟩


end Transformer

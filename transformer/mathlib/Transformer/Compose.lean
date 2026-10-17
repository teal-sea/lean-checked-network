import Transformer.Logits

/-!
# Theorem C: the real-softmax model answers `(a + b) % 113`, given the brute-force facts

`transformer/DESIGN.md` section 8. `mq` below is the quantised model `M_q` written through the
tables: softmax weights `p^h_j = exp(s_j / 2^t) / Σ_j' exp(s_j' / 2^t)` from the integer scores
`s_j = sc[h][j][tok_j]`, then

    mqPre_i    = CI_i / S⁴ + Σ_h Σ_j p^h_j TI[h][j][tok_j]_i / S⁴
    mqHid_i    = max 0 mqPre_i
    mqLogits_k = CU_k / S⁶ + Σ_h Σ_j p^h_j TU[h][j][tok_j]_k / S⁴ + Σ_i mqHid_i G_{i k} / S²

(the residual stream, the MLP and the unembedding of DESIGN.md section 3 with the scales divided
out; `CI`, `CU`, `TI`, `TU`, `G` are the tables of section 6). `realExp_eq_mq` is the identity
`L* = D* S⁶ · logits(M_q)` of section 3: the program run with `e* = 2^f exp((s_j - max s)/2^t)`
equals `D* S⁶` times `mq`, with `D* > 0`. `real_model_adds_mod_113` composes B1, B2 and this
identity with the brute-force facts (Theorem A) taken as hypotheses.
-/

namespace Transformer

/-- The softmax weight of position `j` in head `h`, from the integer scores at unit `2^t`. -/
noncomputable def softmaxW (T : Tables) (t : ℕ) (tok : Fin 3 → Fin 114) (h : Fin 4) (j : Fin 3) :
    ℝ :=
  Real.exp ((T.sc h j (tok j) : ℝ) / 2 ^ t) / ∑ j', Real.exp ((T.sc h j' (tok j') : ℝ) / 2 ^ t)

/-- The pre-activation of hidden unit `i` in `M_q`. -/
noncomputable def mqPre (T : Tables) (S t : ℕ) (tok : Fin 3 → Fin 114) (i : Fin 512) : ℝ :=
  (T.CI i : ℝ) / (S : ℝ) ^ 4
    + (∑ h, ∑ j, softmaxW T t tok h j * (T.TI h j (tok j) i : ℝ)) / (S : ℝ) ^ 4

/-- Hidden unit `i` of `M_q` after the ReLU. -/
noncomputable def mqHid (T : Tables) (S t : ℕ) (tok : Fin 3 → Fin 114) (i : Fin 512) : ℝ :=
  max 0 (mqPre T S t tok i)

/-- Logit `k` of `M_q`. -/
noncomputable def mqLogits (T : Tables) (S t : ℕ) (tok : Fin 3 → Fin 114) (k : Fin 113) : ℝ :=
  (T.CU k : ℝ) / (S : ℝ) ^ 6
    + (∑ h, ∑ j, softmaxW T t tok h j * (T.TU h j (tok j) k : ℝ)) / (S : ℝ) ^ 4
    + (∑ i, mqHid T S t tok i * (T.G i k : ℝ)) / (S : ℝ) ^ 2

/-- The logits of `M_q` on the pair `(a, b)`. -/
noncomputable def mq (T : Tables) (S t : ℕ) (a b : Fin 113) : Fin 113 → ℝ :=
  mqLogits T S t (toks a b)

section identity
variable (p : ExpParams) (T : Tables) (tok : Fin 3 → Fin 114)

theorem eReal_pos (h : Fin 4) (j : Fin 3) : 0 < eReal p T tok h j := by
  unfold eReal; positivity

theorem Dh_eReal_pos (h : Fin 4) : 0 < Dh (eReal p T tok) h := by
  unfold Dh
  exact Finset.sum_pos (fun j _ => eReal_pos p T tok h j) Finset.univ_nonempty

theorem Dprod_eReal_pos : 0 < Dprod (eReal p T tok) := by
  unfold Dprod
  have h := Dh_eReal_pos p T tok
  exact mul_pos (mul_pos (mul_pos (h 0) (h 1)) (h 2)) (h 3)

/-- `e*^h_j = c_h · exp(s_j / 2^t)` with `c_h = 2^f exp(-max s / 2^t)`. -/
theorem eReal_eq (h : Fin 4) (j : Fin 3) :
    eReal p T tok h j =
      (2 ^ p.f * Real.exp (-(smax T tok h : ℝ) / 2 ^ p.t))
        * Real.exp ((T.sc h j (tok j) : ℝ) / 2 ^ p.t) := by
  unfold eReal shifted
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  push_cast
  ring

/-- `e*^h_j / D*^h` is the softmax weight. -/
theorem eReal_div_Dh (h : Fin 4) (j : Fin 3) :
    eReal p T tok h j / Dh (eReal p T tok) h = softmaxW T p.t tok h j := by
  unfold softmaxW Dh
  have hc : 0 < 2 ^ p.f * Real.exp (-(smax T tok h : ℝ) / 2 ^ p.t) := by positivity
  simp only [eReal_eq p T tok h]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ hc.ne']

theorem cof_mul_eReal (h : Fin 4) (j : Fin 3) :
    cof (eReal p T tok) h * eReal p T tok h j = Dprod (eReal p T tok) * softmaxW T p.t tok h j := by
  rw [← eReal_div_Dh, ← cof_mul_Dh (eReal p T tok) h]
  have := (Dh_eReal_pos p T tok h).ne'
  field_simp

theorem att_eReal (t : Fin 4 → Fin 3 → ℝ) :
    att (eReal p T tok) t = Dprod (eReal p T tok) * ∑ h, ∑ j, softmaxW T p.t tok h j * t h j := by
  unfold att
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, cof_mul_eReal, mul_assoc]

variable (S : ℕ) (hS : 0 < S)
include hS

theorem pre_eReal (i : Fin 512) :
    pre T tok (eReal p T tok) i = Dprod (eReal p T tok) * (S : ℝ) ^ 4 * mqPre T S p.t tok i := by
  unfold pre mqPre
  rw [att_eReal]
  have : (S : ℝ) ≠ 0 := by positivity
  field_simp

theorem hid_eReal (i : Fin 512) :
    hid T tok (eReal p T tok) i = Dprod (eReal p T tok) * (S : ℝ) ^ 4 * mqHid T S p.t tok i := by
  unfold hid mqHid
  rw [pre_eReal p T tok S hS]
  have hc : 0 ≤ Dprod (eReal p T tok) * (S : ℝ) ^ 4 := by
    have := Dprod_eReal_pos p T tok
    positivity
  rw [mul_max_of_nonneg _ _ hc, mul_zero]

/-- The identity of DESIGN.md section 3: the real-exp run of the program is `D* S⁶` times the
logits of `M_q`. -/
theorem realExp_eq_mq (k : Fin 113) :
    logits T S tok (eReal p T tok) k = Dprod (eReal p T tok) * (S : ℝ) ^ 6 * mqLogits T S p.t tok k := by
  unfold logits mqLogits
  rw [att_eReal]
  have hsum : ∑ i, hid T tok (eReal p T tok) i * (T.G i k : ℝ)
      = Dprod (eReal p T tok) * (S : ℝ) ^ 4 * ∑ i, mqHid T S p.t tok i * (T.G i k : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hid_eReal p T tok S hS, mul_assoc]
  rw [hsum]
  have : (S : ℝ) ≠ 0 := by positivity
  field_simp

end identity

/-- **Theorem C, with the brute-force facts as hypotheses.** Parameters `p` of `expFix` with the
side conditions of B1, a `δ` at least `deltaBound p`, tables `T` satisfying the bounds `B`, the
scale `S`, and the hypothesis `hA` (Theorem A: on every pair the integer program's logit at
`(a + b) % 113` exceeds every other logit by more than `2 Ebound`). Conclusion: on every pair
the real-softmax model `M_q` (`mq`) has its strict maximum at `(a + b) % 113`, and
`argmaxFirst` (first index on a tie) returns it. -/
theorem real_model_adds_mod_113
    (p : ExpParams) (hn : 0 < p.n) (hm : 0 < p.m) (hR : p.R ≤ 2 ^ p.m)
    (hclamp : (2 : ℝ) ^ p.f ≤ Real.exp p.R)
    (δ : ℕ) (hδ : deltaBound p ≤ δ)
    (T : Tables) (B : Bounds) (hB : T.Bounded B) (S : ℕ) (hS : 0 < S)
    (hA : ∀ a b : Fin 113, ∀ k, k ≠ ans a b →
      intLogits p T S a b k + 2 * (Ebound S p.f δ B : ℤ) < intLogits p T S a b (ans a b)) :
    ∀ a b : Fin 113,
      (∀ k, k ≠ ans a b → mq T S p.t a b k < mq T S p.t a b (ans a b)) ∧
        argmaxFirst (mq T S p.t a b) = ans a b := by
  intro a b
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
    (Ebound S p.f δ B) (ans a b) (hA a b) hclose
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

/-- The same at the chosen configuration: `expFix` with `(t, f, n, m, R) = (32, 32, 16, 5, 24)`,
`δ = 2`, `S = 256`, the bounds of `scan_best_epoch3044.txt`, and `E` the design's literal. -/
theorem real_model_adds_mod_113_chosen (T : Tables) (hB : T.Bounded chosenBounds)
    (hA : ∀ a b : Fin 113, ∀ k, k ≠ ans a b →
      intLogits chosen T 256 a b k
        + 2 * 416063585574805997938804232439435952711840399411200
        < intLogits chosen T 256 a b (ans a b)) :
    ∀ a b : Fin 113,
      (∀ k, k ≠ ans a b → mq T 256 32 a b k < mq T 256 32 a b (ans a b)) ∧
        argmaxFirst (mq T 256 32 a b) = ans a b := by
  have hE : (Ebound 256 chosen.f 2 chosenBounds : ℤ) =
      416063585574805997938804232439435952711840399411200 := by
    show (Ebound 256 32 2 chosenBounds : ℤ) = _
    rw [Ebound_chosen]; rfl
  exact real_model_adds_mod_113 chosen (by decide) (by decide) (by decide) clamp_chosen 2
    deltaBound_chosen T chosenBounds hB 256 (by norm_num)
    (by intro a b k hk; rw [hE]; exact hA a b k hk)

end Transformer

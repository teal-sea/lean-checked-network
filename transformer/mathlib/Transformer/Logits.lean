import Transformer.Program

/-!
# Theorem B2: the logit perturbation bound

`transformer/DESIGN.md` section 5. Two runs of the program (`Program.lean`) on the same tables
with attention weights `e` and `e'` that are each bounded by `Me = 2^f + δ` and differ by at
most `δ` have logits that differ by at most `Ebound`, a number computed from `S`, `f`, `δ` and
bounds on the table entries:

    |TI[h][j][tok]_i| ≤ B.TI h      |TU[h][j][tok]_k| ≤ B.TU h
    |CI_i| ≤ B.CI                   |CU_k| ≤ B.CU                   Σ_i |G_{i k}| ≤ B.G

With `B.TI h = Omax_h ‖Win‖`, `B.TU h = Omax_h ‖U‖`, `B.CI = S² |x₂| ‖Win‖ + |bin|`,
`B.CU = S⁴ |x₂| ‖U‖ + |bout| ‖U‖`, `B.G = ‖Wout‖ ‖U‖` the number `Ebound` is exactly the `E` of
`error_bound_E` in `int_transformer.py` (`Ebound_chosen` below checks the value).
`answer_of_margin` is the corollary: if the integer run's margin exceeds `2 Ebound`, the real
run has the same strict maximum.
-/

namespace Transformer

/-- Bounds on the table entries, as natural numbers. -/
structure Bounds where
  TI : Fin 4 → ℕ
  TU : Fin 4 → ℕ
  CI : ℕ
  CU : ℕ
  G : ℕ

/-- The tables satisfy the bounds. -/
def Tables.Bounded (T : Tables) (B : Bounds) : Prop :=
  (∀ h j tok i, |T.TI h j tok i| ≤ B.TI h) ∧ (∀ h j tok k, |T.TU h j tok k| ≤ B.TU h) ∧
    (∀ i, |T.CI i| ≤ B.CI) ∧ (∀ k, |T.CU k| ≤ B.CU) ∧ (∀ k, ∑ i, |T.G i k| ≤ B.G)

/-- `Me = 2^f + δ` bounds every attention weight. -/
def Me (f δ : ℕ) : ℕ := 2 ^ f + δ
/-- `MD = 3 Me` bounds every denominator `D^h`. -/
def MD (f δ : ℕ) : ℕ := 3 * Me f δ
/-- `dDh = 3 δ` bounds `|D^h - D'^h|`. -/
def dDh (δ : ℕ) : ℕ := 3 * δ
/-- `dD = 4 dDh MD³` bounds `|D - D'|`. -/
def dD (f δ : ℕ) : ℕ := 4 * dDh δ * MD f δ ^ 3
/-- `dc = 3 dDh MD²` bounds `|c^h - c'^h|`. -/
def dc (f δ : ℕ) : ℕ := 3 * dDh δ * MD f δ ^ 2
/-- The attention term's change against a table slice bounded by `Bh`. -/
def dAtt (f δ : ℕ) (Bh : Fin 4 → ℕ) : ℕ :=
  ∑ h, (dc f δ * (3 * Me f δ) * Bh h + MD f δ ^ 3 * (3 * δ) * Bh h)
/-- `dPre` bounds the change of every pre-activation (and, ReLU being 1-Lipschitz, every hidden unit). -/
def dPre (f δ : ℕ) (B : Bounds) : ℕ := dD f δ * B.CI + dAtt f δ B.TI
/-- `Ebound` bounds the change of every logit. -/
def Ebound (S f δ : ℕ) (B : Bounds) : ℕ :=
  dD f δ * B.CU + S ^ 2 * dAtt f δ B.TU + B.G * dPre f δ B

/-- The bounds of the chosen configuration (`q = 8`, `S = 256`), from the norms measured in
`transformer/scan_best_epoch3044.txt`: `Omax = [33001994, 31898447, 33144298, 33210799]`,
`‖Win‖ = 3272`, `|bin| = 520813984`, `‖Wout‖ = 8774`, `|bout| = 71585923072`, `‖U‖ = 2025`,
`|x₂| = 117`. -/
def chosenBounds : Bounds where
  TI := ![33001994 * 3272, 31898447 * 3272, 33144298 * 3272, 33210799 * 3272]
  TU := ![33001994 * 2025, 31898447 * 2025, 33144298 * 2025, 33210799 * 2025]
  CI := 256 ^ 2 * 117 * 3272 + 520813984
  CU := 256 ^ 4 * 117 * 2025 + 71585923072 * 2025
  G := 8774 * 2025

/-- `Ebound` at the chosen configuration is the design's `E`. -/
theorem Ebound_chosen :
    Ebound 256 32 2 chosenBounds = 416063585574805997938804232439435952711840399411200 := by
  simp only [Ebound, dPre, dAtt, dD, dc, MD, Me, dDh, chosenBounds, Fin.sum_univ_four]
  norm_num

theorem abs_mul_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

theorem abs_sum_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) (h : ∀ i ∈ s, |f i| ≤ g i) :
    |∑ i ∈ s, f i| ≤ ∑ i ∈ s, g i :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h)

theorem abs_prod3_sub_le {a1 a2 a3 b1 b2 b3 M ε : ℝ}
    (ha2 : |a2| ≤ M) (ha3 : |a3| ≤ M)
    (hb1 : |b1| ≤ M) (hb2 : |b2| ≤ M)
    (h1 : |a1 - b1| ≤ ε) (h2 : |a2 - b2| ≤ ε) (h3 : |a3 - b3| ≤ ε) :
    |a1 * a2 * a3 - b1 * b2 * b3| ≤ 3 * ε * M ^ 2 := by
  have key : a1 * a2 * a3 - b1 * b2 * b3
      = (a1 - b1) * a2 * a3 + b1 * (a2 - b2) * a3 + b1 * b2 * (a3 - b3) := by ring
  have t1 : |(a1 - b1) * a2 * a3| ≤ ε * M * M := abs_mul_le (abs_mul_le h1 ha2) ha3
  have t2 : |b1 * (a2 - b2) * a3| ≤ M * ε * M := abs_mul_le (abs_mul_le hb1 h2) ha3
  have t3 : |b1 * b2 * (a3 - b3)| ≤ M * M * ε := abs_mul_le (abs_mul_le hb1 hb2) h3
  rw [key]
  calc |(a1 - b1) * a2 * a3 + b1 * (a2 - b2) * a3 + b1 * b2 * (a3 - b3)|
      ≤ |(a1 - b1) * a2 * a3| + |b1 * (a2 - b2) * a3| + |b1 * b2 * (a3 - b3)| :=
        abs_add_three _ _ _
    _ ≤ ε * M * M + M * ε * M + M * M * ε := add_le_add (add_le_add t1 t2) t3
    _ = 3 * ε * M ^ 2 := by ring

theorem abs_prod4_sub_le {a1 a2 a3 a4 b1 b2 b3 b4 M ε : ℝ}
    (ha2 : |a2| ≤ M) (ha3 : |a3| ≤ M) (ha4 : |a4| ≤ M)
    (hb1 : |b1| ≤ M) (hb2 : |b2| ≤ M) (hb3 : |b3| ≤ M)
    (h1 : |a1 - b1| ≤ ε) (h2 : |a2 - b2| ≤ ε) (h3 : |a3 - b3| ≤ ε) (h4 : |a4 - b4| ≤ ε) :
    |a1 * a2 * a3 * a4 - b1 * b2 * b3 * b4| ≤ 4 * ε * M ^ 3 := by
  have key : a1 * a2 * a3 * a4 - b1 * b2 * b3 * b4
      = (a1 * a2 * a3 - b1 * b2 * b3) * a4 + b1 * b2 * b3 * (a4 - b4) := by ring
  have t1 : |(a1 * a2 * a3 - b1 * b2 * b3) * a4| ≤ 3 * ε * M ^ 2 * M :=
    abs_mul_le (abs_prod3_sub_le ha2 ha3 hb1 hb2 h1 h2 h3) ha4
  have t2 : |b1 * b2 * b3 * (a4 - b4)| ≤ M * M * M * ε :=
    abs_mul_le (abs_mul_le (abs_mul_le hb1 hb2) hb3) h4
  rw [key]
  calc |(a1 * a2 * a3 - b1 * b2 * b3) * a4 + b1 * b2 * b3 * (a4 - b4)|
      ≤ |(a1 * a2 * a3 - b1 * b2 * b3) * a4| + |b1 * b2 * b3 * (a4 - b4)| := abs_add_le _ _
    _ ≤ 3 * ε * M ^ 2 * M + M * M * M * ε := add_le_add t1 t2
    _ = 4 * ε * M ^ 3 := by ring

section chain
variable {M ε : ℝ} (e e' : Fin 4 → Fin 3 → ℝ)

theorem Dh_abs_le (he : ∀ h j, |e h j| ≤ M) (h : Fin 4) : |Dh e h| ≤ 3 * M := by
  unfold Dh
  rw [Fin.sum_univ_three]
  calc |e h 0 + e h 1 + e h 2| ≤ |e h 0| + |e h 1| + |e h 2| := abs_add_three _ _ _
    _ ≤ M + M + M := add_le_add (add_le_add (he h 0) (he h 1)) (he h 2)
    _ = 3 * M := by ring

theorem Dh_sub_le (hd : ∀ h j, |e h j - e' h j| ≤ ε) (h : Fin 4) :
    |Dh e h - Dh e' h| ≤ 3 * ε := by
  unfold Dh
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  calc |e h 0 + e h 1 + e h 2 - (e' h 0 + e' h 1 + e' h 2)|
      = |(e h 0 - e' h 0) + (e h 1 - e' h 1) + (e h 2 - e' h 2)| := by ring_nf
    _ ≤ |e h 0 - e' h 0| + |e h 1 - e' h 1| + |e h 2 - e' h 2| := abs_add_three _ _ _
    _ ≤ ε + ε + ε := add_le_add (add_le_add (hd h 0) (hd h 1)) (hd h 2)
    _ = 3 * ε := by ring

theorem Dprod_sub_le (he : ∀ h j, |e h j| ≤ M) (he' : ∀ h j, |e' h j| ≤ M)
    (hd : ∀ h j, |e h j - e' h j| ≤ ε) :
    |Dprod e - Dprod e'| ≤ 4 * (3 * ε) * (3 * M) ^ 3 := by
  unfold Dprod
  exact abs_prod4_sub_le (Dh_abs_le e he 1) (Dh_abs_le e he 2)
    (Dh_abs_le e he 3) (Dh_abs_le e' he' 0) (Dh_abs_le e' he' 1) (Dh_abs_le e' he' 2)
    (Dh_sub_le e e' hd 0) (Dh_sub_le e e' hd 1) (Dh_sub_le e e' hd 2) (Dh_sub_le e e' hd 3)

theorem cof_abs_le (he : ∀ h j, |e h j| ≤ M) : ∀ h, |cof e h| ≤ (3 * M) ^ 3
  | 0 => by
    simp only [cof]
    calc _ ≤ (3 * M) * (3 * M) * (3 * M) :=
          abs_mul_le (abs_mul_le (Dh_abs_le e he 1) (Dh_abs_le e he 2)) (Dh_abs_le e he 3)
      _ = (3 * M) ^ 3 := by ring
  | 1 => by
    simp only [cof]
    calc _ ≤ (3 * M) * (3 * M) * (3 * M) :=
          abs_mul_le (abs_mul_le (Dh_abs_le e he 0) (Dh_abs_le e he 2)) (Dh_abs_le e he 3)
      _ = (3 * M) ^ 3 := by ring
  | 2 => by
    simp only [cof]
    calc _ ≤ (3 * M) * (3 * M) * (3 * M) :=
          abs_mul_le (abs_mul_le (Dh_abs_le e he 0) (Dh_abs_le e he 1)) (Dh_abs_le e he 3)
      _ = (3 * M) ^ 3 := by ring
  | 3 => by
    simp only [cof]
    calc _ ≤ (3 * M) * (3 * M) * (3 * M) :=
          abs_mul_le (abs_mul_le (Dh_abs_le e he 0) (Dh_abs_le e he 1)) (Dh_abs_le e he 2)
      _ = (3 * M) ^ 3 := by ring

theorem cof_sub_le (he : ∀ h j, |e h j| ≤ M) (he' : ∀ h j, |e' h j| ≤ M)
    (hd : ∀ h j, |e h j - e' h j| ≤ ε) :
    ∀ h, |cof e h - cof e' h| ≤ 3 * (3 * ε) * (3 * M) ^ 2
  | 0 => by
    simp only [cof]
    exact abs_prod3_sub_le (Dh_abs_le e he 2) (Dh_abs_le e he 3)
      (Dh_abs_le e' he' 1) (Dh_abs_le e' he' 2)
      (Dh_sub_le e e' hd 1) (Dh_sub_le e e' hd 2) (Dh_sub_le e e' hd 3)
  | 1 => by
    simp only [cof]
    exact abs_prod3_sub_le (Dh_abs_le e he 2) (Dh_abs_le e he 3)
      (Dh_abs_le e' he' 0) (Dh_abs_le e' he' 2)
      (Dh_sub_le e e' hd 0) (Dh_sub_le e e' hd 2) (Dh_sub_le e e' hd 3)
  | 2 => by
    simp only [cof]
    exact abs_prod3_sub_le (Dh_abs_le e he 1) (Dh_abs_le e he 3)
      (Dh_abs_le e' he' 0) (Dh_abs_le e' he' 1)
      (Dh_sub_le e e' hd 0) (Dh_sub_le e e' hd 1) (Dh_sub_le e e' hd 3)
  | 3 => by
    simp only [cof]
    exact abs_prod3_sub_le (Dh_abs_le e he 1) (Dh_abs_le e he 2)
      (Dh_abs_le e' he' 0) (Dh_abs_le e' he' 1)
      (Dh_sub_le e e' hd 0) (Dh_sub_le e e' hd 1) (Dh_sub_le e e' hd 2)

/-- `|Σ_j e^h_j t_{h j}| ≤ 3 M B_h`. -/
theorem wsum_abs_le (he : ∀ h j, |e h j| ≤ M) (t : Fin 4 → Fin 3 → ℝ) (Bt : Fin 4 → ℝ)
    (ht : ∀ h j, |t h j| ≤ Bt h) (h : Fin 4) :
    |∑ j, e h j * t h j| ≤ 3 * M * Bt h := by
  calc |∑ j, e h j * t h j| ≤ ∑ j : Fin 3, M * Bt h :=
        abs_sum_le _ _ _ (fun j _ => abs_mul_le (he h j) (ht h j))
    _ = 3 * M * Bt h := by simp [Finset.sum_const]; ring

theorem wsum_sub_le (hd : ∀ h j, |e h j - e' h j| ≤ ε) (t : Fin 4 → Fin 3 → ℝ)
    (Bt : Fin 4 → ℝ) (ht : ∀ h j, |t h j| ≤ Bt h) (h : Fin 4) :
    |∑ j, e h j * t h j - ∑ j, e' h j * t h j| ≤ 3 * ε * Bt h := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ j, (e h j * t h j - e' h j * t h j)| ≤ ∑ j : Fin 3, ε * Bt h :=
        abs_sum_le _ _ _ (fun j _ => by
          rw [← sub_mul]; exact abs_mul_le (hd h j) (ht h j))
    _ = 3 * ε * Bt h := by simp [Finset.sum_const]; ring

/-- The attention term against a slice `t` with `|t h j| ≤ Bt h` changes by at most
`Σ_h (dc · 3 M · Bt h + MD³ · 3 ε · Bt h)`. -/
theorem att_sub_le (he : ∀ h j, |e h j| ≤ M) (he' : ∀ h j, |e' h j| ≤ M)
    (hd : ∀ h j, |e h j - e' h j| ≤ ε) (t : Fin 4 → Fin 3 → ℝ) (Bt : Fin 4 → ℝ)
    (ht : ∀ h j, |t h j| ≤ Bt h) :
    |att e t - att e' t| ≤
      ∑ h, (3 * (3 * ε) * (3 * M) ^ 2 * (3 * M) * Bt h + (3 * M) ^ 3 * (3 * ε) * Bt h) := by
  unfold att
  rw [← Finset.sum_sub_distrib]
  apply abs_sum_le
  intro h _
  have key : cof e h * ∑ j, e h j * t h j - cof e' h * ∑ j, e' h j * t h j
      = (cof e h - cof e' h) * ∑ j, e h j * t h j
        + cof e' h * (∑ j, e h j * t h j - ∑ j, e' h j * t h j) := by ring
  rw [key]
  calc _ ≤ |(cof e h - cof e' h) * ∑ j, e h j * t h j|
          + |cof e' h * (∑ j, e h j * t h j - ∑ j, e' h j * t h j)| := abs_add_le _ _
    _ ≤ 3 * (3 * ε) * (3 * M) ^ 2 * (3 * M * Bt h) + (3 * M) ^ 3 * (3 * ε * Bt h) :=
        add_le_add (abs_mul_le (cof_sub_le e e' he he' hd h) (wsum_abs_le e he t Bt ht h))
          (abs_mul_le (cof_abs_le e' he' h) (wsum_sub_le e e' hd t Bt ht h))
    _ = _ := by ring

end chain

/-- The real constants of the chain, as casts of the natural ones. -/
theorem dAtt_cast (f δ : ℕ) (Bh : Fin 4 → ℕ) :
    (dAtt f δ Bh : ℝ) = ∑ h, (3 * (3 * (δ : ℝ)) * (3 * (Me f δ : ℝ)) ^ 2 * (3 * (Me f δ : ℝ)) * Bh h
      + (3 * (Me f δ : ℝ)) ^ 3 * (3 * (δ : ℝ)) * Bh h) := by
  simp only [dAtt, dc, MD, dDh]
  push_cast
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- **Theorem B2.** Two runs of the program whose attention weights are bounded by `Me f δ` and
differ by at most `δ` have logits within `Ebound S f δ B` of each other. -/
theorem logits_close (T : Tables) (B : Bounds) (hB : T.Bounded B) (S f δ : ℕ)
    (tok : Fin 3 → Fin 114) (e e' : Fin 4 → Fin 3 → ℝ)
    (he : ∀ h j, |e h j| ≤ Me f δ) (he' : ∀ h j, |e' h j| ≤ Me f δ)
    (hd : ∀ h j, |e h j - e' h j| ≤ δ) (k : Fin 113) :
    |logits T S tok e k - logits T S tok e' k| ≤ Ebound S f δ B := by
  obtain ⟨hTI, hTU, hCI, hCU, hG⟩ := hB
  set M : ℝ := (Me f δ : ℝ) with hM
  set ε : ℝ := (δ : ℝ) with hε
  have hD := Dprod_sub_le e e' he he' hd
  -- the pre-activations
  have hpre : ∀ i, |pre T tok e i - pre T tok e' i| ≤ dPre f δ B := by
    intro i
    unfold pre
    have hTIi : ∀ h j, |(T.TI h j (tok j) i : ℝ)| ≤ (B.TI h : ℝ) := by
      intro h j; exact_mod_cast hTI h j (tok j) i
    have hatt := att_sub_le e e' he he' hd (fun h j => (T.TI h j (tok j) i : ℝ))
      (fun h => (B.TI h : ℝ)) hTIi
    have hCIi : |(T.CI i : ℝ)| ≤ (B.CI : ℝ) := by exact_mod_cast hCI i
    have key : Dprod e * (T.CI i : ℝ) + att e (fun h j => (T.TI h j (tok j) i : ℝ))
        - (Dprod e' * (T.CI i : ℝ) + att e' (fun h j => (T.TI h j (tok j) i : ℝ)))
        = (Dprod e - Dprod e') * (T.CI i : ℝ)
          + (att e (fun h j => (T.TI h j (tok j) i : ℝ))
            - att e' (fun h j => (T.TI h j (tok j) i : ℝ))) := by ring
    rw [key]
    calc _ ≤ |(Dprod e - Dprod e') * (T.CI i : ℝ)|
            + |att e (fun h j => (T.TI h j (tok j) i : ℝ))
              - att e' (fun h j => (T.TI h j (tok j) i : ℝ))| := abs_add_le _ _
      _ ≤ 4 * (3 * ε) * (3 * M) ^ 3 * (B.CI : ℝ) + _ := add_le_add (abs_mul_le hD hCIi) hatt
      _ = dPre f δ B := by
          simp only [dPre, dD, dDh, MD]
          push_cast
          rw [dAtt_cast]
  have hhid : ∀ i, |hid T tok e i - hid T tok e' i| ≤ dPre f δ B := by
    intro i
    unfold hid
    rw [max_comm 0, max_comm 0]
    exact (abs_max_sub_max_le_abs _ _ _).trans (hpre i)
  -- the logits
  unfold logits
  have hTUk : ∀ h j, |(T.TU h j (tok j) k : ℝ)| ≤ (B.TU h : ℝ) := by
    intro h j; exact_mod_cast hTU h j (tok j) k
  have hatt := att_sub_le e e' he he' hd (fun h j => (T.TU h j (tok j) k : ℝ))
    (fun h => (B.TU h : ℝ)) hTUk
  have hCUk : |(T.CU k : ℝ)| ≤ (B.CU : ℝ) := by exact_mod_cast hCU k
  have hGk : ∑ i, |(T.G i k : ℝ)| ≤ (B.G : ℝ) := by
    have := hG k
    exact_mod_cast this
  have hGsum : |∑ i, hid T tok e i * (T.G i k : ℝ) - ∑ i, hid T tok e' i * (T.G i k : ℝ)|
      ≤ (dPre f δ B : ℝ) * B.G := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ i, (dPre f δ B : ℝ) * |(T.G i k : ℝ)| :=
          abs_sum_le _ _ _ (fun i _ => by
            rw [← sub_mul, abs_mul]
            exact mul_le_mul_of_nonneg_right (hhid i) (abs_nonneg _))
      _ = (dPre f δ B : ℝ) * ∑ i, |(T.G i k : ℝ)| := by rw [Finset.mul_sum]
      _ ≤ (dPre f δ B : ℝ) * B.G := by gcongr
  have key : Dprod e * (T.CU k : ℝ) + (S : ℝ) ^ 2 * att e (fun h j => (T.TU h j (tok j) k : ℝ))
        + ∑ i, hid T tok e i * (T.G i k : ℝ)
      - (Dprod e' * (T.CU k : ℝ) + (S : ℝ) ^ 2 * att e' (fun h j => (T.TU h j (tok j) k : ℝ))
        + ∑ i, hid T tok e' i * (T.G i k : ℝ))
      = (Dprod e - Dprod e') * (T.CU k : ℝ)
        + (S : ℝ) ^ 2 * (att e (fun h j => (T.TU h j (tok j) k : ℝ))
            - att e' (fun h j => (T.TU h j (tok j) k : ℝ)))
        + (∑ i, hid T tok e i * (T.G i k : ℝ) - ∑ i, hid T tok e' i * (T.G i k : ℝ)) := by ring
  rw [key]
  have hS : |(S : ℝ) ^ 2| = (S : ℝ) ^ 2 := abs_of_nonneg (by positivity)
  calc _ ≤ |(Dprod e - Dprod e') * (T.CU k : ℝ)|
          + |(S : ℝ) ^ 2 * (att e (fun h j => (T.TU h j (tok j) k : ℝ))
              - att e' (fun h j => (T.TU h j (tok j) k : ℝ)))|
          + |∑ i, hid T tok e i * (T.G i k : ℝ) - ∑ i, hid T tok e' i * (T.G i k : ℝ)| :=
        abs_add_three _ _ _
    _ ≤ 4 * (3 * ε) * (3 * M) ^ 3 * (B.CU : ℝ) + (S : ℝ) ^ 2 * _ + (dPre f δ B : ℝ) * B.G :=
        add_le_add (add_le_add (abs_mul_le hD hCUk) (abs_mul_le hS.le hatt)) hGsum
    _ = Ebound S f δ B := by
        simp only [Ebound, dD, dDh, MD]
        push_cast
        rw [dAtt_cast]
        ring

/-- The corollary: if the integer run has a margin above `2 E` at `r` and the real run is within
`E` of it in every logit, the real run has its strict maximum at `r`. -/
theorem strict_max_of_margin (L : Fin 113 → ℤ) (L' : Fin 113 → ℝ) (E : ℕ) (r : Fin 113)
    (hmargin : ∀ k, k ≠ r → L k + 2 * (E : ℤ) < L r)
    (hclose : ∀ k, |(L k : ℝ) - L' k| ≤ E) :
    ∀ k, k ≠ r → L' k < L' r := by
  intro k hk
  have h1 := hclose k
  have h2 := hclose r
  rw [abs_le] at h1 h2
  have h3 : (L k : ℝ) + 2 * E < L r := by exact_mod_cast hmargin k hk
  linarith [h1.1, h1.2, h2.1, h2.2]

end Transformer

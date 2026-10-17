import TransformerBridge.Bridge
import TransformerCore.BoundsLib

/-!
Transfer the frozen, split core certificates to the Mathlib bounds. The core sources
are mechanically renamed and recompiled on this project's stable toolchain. In
particular the last conjunct uses certified column sums, not entrywise estimates.
-/
namespace TransformerBridge

open TransformerCore (Tab Bnd nth vecOk tablesOk colAbsSum)

/-- Defaulted lookup preserves a signed entry bound, including outside the list. -/
theorem absBnd_nth {v : List ℤ} {b : ℕ} (hv : TransformerCore.AbsBnd b v) (i : ℕ) :
    |nth 0 v i| ≤ (b : ℤ) := by
  induction v generalizing i with
  | nil => simp [nth]
  | cons x xs ih =>
    cases i with
    | zero =>
      exact abs_le.mpr (hv x (by simp))
    | succ i =>
      exact ih (i := i) (fun y hy => hv y (by simp [hy]))

/-- A core vector certificate bounds every defaulted lookup. -/
theorem vecOk_abs_nth {v : List ℤ} {n b : ℕ} (hv : vecOk n b v = true) (i : ℕ) :
    |nth 0 v i| ≤ (b : ℤ) :=
  absBnd_nth ((TransformerCore.vecOk_iff n b v).mp hv).2 i

/-- The natural absolute value used by the core is integer absolute value after casting. -/
theorem natAbs_cast (z : ℤ) : (z.natAbs : ℤ) = |z| := by
  exact Int.natCast_natAbs z

/-- The recursive core column sum is the integer sum over its row indices. -/
theorem colAbsSum_eq_sum_range (G : List (List ℤ)) (k : ℕ) :
    (colAbsSum G k : ℤ) = ∑ i ∈ Finset.range G.length, |nth 0 (nth [] G i) k| := by
  induction G with
  | nil => simp [colAbsSum]
  | cons r rs ih =>
    simp [colAbsSum, List.length_cons, Finset.sum_range_succ', nth, ih, natAbs_cast]

/-- Exact Fin-indexed column-sum transfer; no per-entry relaxation is used. -/
theorem sum_fin_eq_colAbsSum (G : List (List ℤ)) (n : ℕ) (hlen : G.length = n) (k : ℕ) :
    (∑ i : Fin n, |nth 0 (nth [] G i) k|) = (colAbsSum G k : ℤ) := by
  rw [colAbsSum_eq_sum_range, hlen, Finset.sum_range]

/-- Reusable transfer from the core vector and column certificates. -/
theorem bounded_of_core (T : Tab) (bd : Bnd) (B : Transformer.Bounds)
    (ht : tablesOk T bd = true) (hlen : T.G.length = 512)
    (hTI : ∀ h, bd.kTI ≤ B.TI h) (hTU : ∀ h, bd.kTU ≤ B.TU h)
    (hCI : bd.kCI ≤ B.CI) (hCU : bd.kCU ≤ B.CU)
    (hcols : ∀ k, k < 113 → colAbsSum T.G k ≤ B.G) :
    (toTables T).Bounded B := by
  obtain ⟨hcI, hcU, _⟩ := TransformerCore.tablesOk_const T bd ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h j tok i
    obtain ⟨v0, v1, v2, _, _, _⟩ :=
      TransformerCore.tablesOk_facts T bd ht h tok h.isLt tok.isLt
    have hb : (bd.kTI : ℤ) ≤ (B.TI h : ℤ) := by exact_mod_cast hTI h
    fin_cases j
    · exact (vecOk_abs_nth v0 i).trans hb
    · exact (vecOk_abs_nth v1 i).trans hb
    · change |if tok = 113 then nth 0 (nth [] T.TI2 h) i else 0| ≤ (B.TI h : ℤ)
      split_ifs
      · exact (vecOk_abs_nth v2 i).trans hb
      · simp
  · intro h j tok k
    obtain ⟨_, _, _, v0, v1, v2⟩ :=
      TransformerCore.tablesOk_facts T bd ht h tok h.isLt tok.isLt
    have hb : (bd.kTU : ℤ) ≤ (B.TU h : ℤ) := by exact_mod_cast hTU h
    fin_cases j
    · exact (vecOk_abs_nth v0 k).trans hb
    · exact (vecOk_abs_nth v1 k).trans hb
    · change |if tok = 113 then nth 0 (nth [] T.TU2 h) k else 0| ≤ (B.TU h : ℤ)
      split_ifs
      · exact (vecOk_abs_nth v2 k).trans hb
      · simp
  · intro i
    exact (vecOk_abs_nth hcI i).trans (by exact_mod_cast hCI)
  · intro k
    exact (vecOk_abs_nth hcU k).trans (by exact_mod_cast hCU)
  · intro k
    change (∑ i : Fin 512, |nth 0 (nth [] T.G i) k|) ≤ (B.G : ℤ)
    rw [sum_fin_eq_colAbsSum T.G 512 hlen k]
    exact_mod_cast hcols k k.isLt

end TransformerBridge

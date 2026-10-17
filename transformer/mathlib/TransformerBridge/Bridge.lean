import Transformer.Compose
import TransformerCore.Equiv

/-!
# The bridge from the packed core program to the Fin-indexed Mathlib program

`TransformerCore` is the retained core-Lean development (`lean/Transformer/{Model,Fast,Equiv}.lean`, renamed by
`sync_core.sh`): the list-based integer program `logits`, the packed evaluator `fastCheck`, and
`fastCheck_correct`. `Transformer` is the Mathlib development: the Fin-indexed program `intLogits` and
Theorem C about the real-softmax model. This file proves that they are the same program:

* `toTables T` reads a list-based table `T : Tab` as the Fin-indexed `Transformer.Tables`;
* `expFix_eq`: the core `expFix` at `cfgOf p S` is the Mathlib `expFix p`;
* `logits_nth_eq`: entry `k` of the core `logits` is `intLogits p (toTables T) S a b k`;
* `hA_of_fastCheck`: if `fastCheck` passes at `(a, b)` and `tablesOk` holds, then on that pair the right
  logit of `intLogits` beats every other by more than `E2`, which is hypothesis `hA` of Theorem C.

No axiom, no `sorry`, no computation outside the kernel.
-/

namespace TransformerBridge

open TransformerCore (Cfg Tab nth vadd smulN lincombN headE headI headU preAct dens den maxI maxExcept
  maxExceptFrom tablesOk fastCheck Bnd)

/-! ## The configuration -/

/-- The core configuration of `expFix` parameters `p` at scale `S`. -/
def cfgOf (p : Transformer.ExpParams) (S : ℕ) : Cfg where
  S2 := S ^ 2
  f2 := 2 ^ p.f
  lo := p.R * 2 ^ p.t
  pw := 2 ^ p.m
  cs := Transformer.coeffs p
  Fpow := Transformer.bigF p ^ 2 ^ p.m

theorem horner_eq (l : List ℕ) (x : ℤ) :
    TransformerCore.horner l x = Transformer.horner l x := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp only [TransformerCore.horner, Transformer.horner, ih] <;> rfl

theorem expFix_eq (p : Transformer.ExpParams) (S : ℕ) (x : ℤ) :
    TransformerCore.expFix (cfgOf p S) x = Transformer.expFix p x := by
  unfold TransformerCore.expFix Transformer.expFix
  have h : Int.neg (Int.ofNat (cfgOf p S).lo) = -((p.R : ℤ) * 2 ^ p.t) := by
    show -(((p.R * 2 ^ p.t : ℕ)) : ℤ) = -((p.R : ℤ) * 2 ^ p.t)
    first | norm_num | (push_cast; ring) | simp
  rw [h]
  simp only [cfgOf, horner_eq]

theorem maxI_eq_max (x y : ℤ) : TransformerCore.maxI x y = max x y := by
  unfold TransformerCore.maxI
  split_ifs with h
  · exact (max_eq_right h.le).symm
  · exact (max_eq_left (not_lt.1 h)).symm

/-! ## The tables -/

/-- The list-based tables `T` read as Fin-indexed tables; position 2 is filled at token 113 only, as `rawTables`. -/
def toTables (T : Tab) : Transformer.Tables where
  sc h j tk := match j with
    | 0 => nth 0 (nth [] T.sc0 h) tk
    | 1 => nth 0 (nth [] T.sc1 h) tk
    | 2 => if tk = 113 then nth 0 T.sc2 h else 0
  TI h j tk i := match j with
    | 0 => nth 0 (nth [] (nth [] T.TI0 h) tk) i
    | 1 => nth 0 (nth [] (nth [] T.TI1 h) tk) i
    | 2 => if tk = 113 then nth 0 (nth [] T.TI2 h) i else 0
  TU h j tk k := match j with
    | 0 => nth 0 (nth [] (nth [] T.TU0 h) tk) k
    | 1 => nth 0 (nth [] (nth [] T.TU1 h) tk) k
    | 2 => if tk = 113 then nth 0 (nth [] T.TU2 h) k else 0
  CI i := nth 0 T.CI i
  CU k := nth 0 T.CU k
  G i k := nth 0 (nth [] T.G i) k

/-- Numerals in `Fin 4` have the expected values. -/
theorem v0 : ((0 : Fin 4) : ℕ) = 0 := rfl
theorem v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
theorem v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
theorem v3 : ((3 : Fin 4) : ℕ) = 3 := rfl

section slots
variable (T : Tab) (a b : Fin 113)

theorem sc_slot0 (h : Fin 4) : (toTables T).sc h 0 (Transformer.toks a b 0) = nth 0 (nth [] T.sc0 h) a := rfl
theorem sc_slot1 (h : Fin 4) : (toTables T).sc h 1 (Transformer.toks a b 1) = nth 0 (nth [] T.sc1 h) b := rfl
theorem sc_slot2 (h : Fin 4) : (toTables T).sc h 2 (Transformer.toks a b 2) = nth 0 T.sc2 h := rfl
theorem TI_slot0 (h : Fin 4) (i : Fin 512) :
    (toTables T).TI h 0 (Transformer.toks a b 0) i = nth 0 (nth [] (nth [] T.TI0 h) a) i := rfl
theorem TI_slot1 (h : Fin 4) (i : Fin 512) :
    (toTables T).TI h 1 (Transformer.toks a b 1) i = nth 0 (nth [] (nth [] T.TI1 h) b) i := rfl
theorem TI_slot2 (h : Fin 4) (i : Fin 512) :
    (toTables T).TI h 2 (Transformer.toks a b 2) i = nth 0 (nth [] T.TI2 h) i := rfl
theorem TU_slot0 (h : Fin 4) (k : Fin 113) :
    (toTables T).TU h 0 (Transformer.toks a b 0) k = nth 0 (nth [] (nth [] T.TU0 h) a) k := rfl
theorem TU_slot1 (h : Fin 4) (k : Fin 113) :
    (toTables T).TU h 1 (Transformer.toks a b 1) k = nth 0 (nth [] (nth [] T.TU1 h) b) k := rfl
theorem TU_slot2 (h : Fin 4) (k : Fin 113) :
    (toTables T).TU h 2 (Transformer.toks a b 2) k = nth 0 (nth [] T.TU2 h) k := rfl

theorem CI_slot (i : Fin 512) : (toTables T).CI i = nth 0 T.CI i := rfl
theorem CU_slot (k : Fin 113) : (toTables T).CU k = nth 0 T.CU k := rfl
theorem G_slot (i : Fin 512) (k : Fin 113) : (toTables T).G i k = nth 0 (nth [] T.G i) k := rfl

end slots

theorem cfgOf_S2 (p : Transformer.ExpParams) (S : ℕ) : (cfgOf p S).S2 = S ^ 2 := rfl

/-! ## Entries of the list operations -/

theorem nth_vadd (u v : List ℤ) (k : ℕ) : nth 0 (vadd u v) k = nth 0 u k + nth 0 v k := by
  induction u generalizing v k with
  | nil => simp [vadd, nth]
  | cons x xs ih =>
    cases v with
    | nil => simp [vadd, nth]
    | cons y ys =>
      cases k with
      | zero => simp [vadd, nth, Int.add_def]
      | succ k => simp [vadd, nth, ih]

theorem nth_smulN (c : ℕ) (v : List ℤ) (k : ℕ) : nth 0 (smulN c v) k = (c : ℤ) * nth 0 v k := by
  induction v generalizing k with
  | nil => simp [smulN, nth]
  | cons x xs ih => cases k <;> simp_all [smulN, nth, Int.mul_def]

theorem nth_headVec (e : ℕ × ℕ × ℕ) (v0 v1 v2 : List ℤ) (k : ℕ) :
    nth 0 (TransformerCore.headVec e v0 v1 v2) k
      = (e.1 : ℤ) * nth 0 v0 k + ((e.2.1 : ℤ) * nth 0 v1 k + (e.2.2 : ℤ) * nth 0 v2 k) := by
  simp only [TransformerCore.headVec, nth_vadd, nth_smulN]

theorem toNat_cast_eq_max (z : ℤ) : ((Int.toNat z : ℕ) : ℤ) = max 0 z := by omega

theorem nth_map_toNat (L : List ℤ) (k : ℕ) : nth 0 (L.map Int.toNat) k = Int.toNat (nth 0 L k) := by
  induction L generalizing k with
  | nil => simp [nth]
  | cons x xs ih => cases k <;> simp [nth, ih]

/-- Entry `k` of `lincombN cs rs` is the sum over any `n` at least the number of rows. -/
theorem nth_lincombN (cs : List ℕ) (rs : List (List ℤ)) (k n : ℕ) (hn : rs.length ≤ n) :
    nth 0 (lincombN cs rs) k = ∑ i ∈ Finset.range n, (nth 0 cs i : ℤ) * nth 0 (nth [] rs i) k := by
  induction cs generalizing rs n with
  | nil => simp [lincombN, nth]
  | cons c cs ih =>
    cases rs with
    | nil => simp [lincombN, nth]
    | cons r rs =>
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hn; omega⟩
      have hn' : rs.length ≤ n' := by simp at hn; omega
      simp only [lincombN, nth_vadd, nth_smulN, ih rs n' hn', Finset.sum_range_succ', nth]
      ring

/-! ## The attention weights -/

/-- The integer attention weight `expFix (s_j - max s)` of head `h`, position `j`, as a natural number. -/
abbrev eN (p : Transformer.ExpParams) (T : Tab) (a b : Fin 113) (h : Fin 4) (j : Fin 3) : ℕ :=
  Transformer.expFix p (Transformer.shifted (toTables T) (Transformer.toks a b) h j)

theorem headE_eq (p : Transformer.ExpParams) (S : ℕ) (T : Tab) (a b : Fin 113) (h : Fin 4) :
    headE (cfgOf p S) T a b h = (eN p T a b h 0, eN p T a b h 1, eN p T a b h 2) := by
  have hs : Transformer.smax (toTables T) (Transformer.toks a b) h
      = maxI (nth 0 (nth [] T.sc0 h) a) (maxI (nth 0 (nth [] T.sc1 h) b) (nth 0 T.sc2 h)) := by
    unfold Transformer.smax
    rw [maxI_eq_max, maxI_eq_max, ← max_assoc]
    all_goals rfl
  simp only [TransformerCore.headE, eN, Transformer.shifted, hs, expFix_eq] <;> rfl

/-! ## The pre-activations and the logits -/

section entries
variable (p : Transformer.ExpParams) (S : ℕ) (T : Tab) (a b : Fin 113)

theorem preAct_eq (i : Fin 512) :
    nth 0 (preAct (cfgOf p S) T a b) i
      = Transformer.pre (toTables T) (Transformer.toks a b)
          (Transformer.eInt p (toTables T) (Transformer.toks a b)) i := by
  have e0 : headE (cfgOf p S) T a b 0 = (eN p T a b 0 0, eN p T a b 0 1, eN p T a b 0 2) := headE_eq p S T a b 0
  have e1 : headE (cfgOf p S) T a b 1 = (eN p T a b 1 0, eN p T a b 1 1, eN p T a b 1 2) := headE_eq p S T a b 1
  have e2 : headE (cfgOf p S) T a b 2 = (eN p T a b 2 0, eN p T a b 2 1, eN p T a b 2 2) := headE_eq p S T a b 2
  have e3 : headE (cfgOf p S) T a b 3 = (eN p T a b 3 0, eN p T a b 3 1, eN p T a b 3 2) := headE_eq p S T a b 3
  simp only [TransformerCore.preAct, TransformerCore.headI, e0, e1, e2, e3, dens, den, nth_vadd, nth_smulN,
    nth_headVec]
  simp only [Transformer.pre, Transformer.att, Transformer.Dprod, Transformer.Dh, Transformer.cof,
    Transformer.eInt, Fin.sum_univ_four, Fin.sum_univ_three, TI_slot0, TI_slot1, TI_slot2, CI_slot, v0, v1, v2, v3,
    Int.cast_id]
  push_cast
  ring

theorem logits_nth_eq (hG : T.G.length = 512) (k : Fin 113) :
    nth 0 (TransformerCore.logits (cfgOf p S) T a b) k = Transformer.intLogits p (toTables T) S a b k := by
  have e0 : headE (cfgOf p S) T a b 0 = (eN p T a b 0 0, eN p T a b 0 1, eN p T a b 0 2) := headE_eq p S T a b 0
  have e1 : headE (cfgOf p S) T a b 1 = (eN p T a b 1 0, eN p T a b 1 1, eN p T a b 1 2) := headE_eq p S T a b 1
  have e2 : headE (cfgOf p S) T a b 2 = (eN p T a b 2 0, eN p T a b 2 1, eN p T a b 2 2) := headE_eq p S T a b 2
  have e3 : headE (cfgOf p S) T a b 3 = (eN p T a b 3 0, eN p T a b 3 1, eN p T a b 3 2) := headE_eq p S T a b 3
  have hlin : nth 0 (lincombN ((preAct (cfgOf p S) T a b).map Int.toNat) T.G) k
      = ∑ i : Fin 512, Transformer.hid (toTables T) (Transformer.toks a b)
          (Transformer.eInt p (toTables T) (Transformer.toks a b)) i * ((toTables T).G i k : ℤ) := by
    rw [nth_lincombN _ _ _ 512 (le_of_eq hG), Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [nth_map_toNat, preAct_eq, toNat_cast_eq_max, Transformer.hid]
    all_goals rfl
  unfold TransformerCore.logits
  simp only [e0, e1, e2, e3, dens, den, nth_vadd, nth_smulN, hlin, headU, nth_headVec, cfgOf_S2]
  unfold Transformer.intLogits Transformer.logits
  simp only [Transformer.att, Transformer.Dprod, Transformer.Dh, Transformer.cof, Transformer.eInt,
    Fin.sum_univ_four, Fin.sum_univ_three, TU_slot0, TU_slot1, TU_slot2, CU_slot, G_slot, v0, v1, v2, v3, Int.cast_id]
  push_cast
  ring

end entries

/-! ## From a passing `fastCheck` to the hypothesis `hA` -/

theorem maxExceptFrom_ge_acc (xs : List ℤ) (i c : ℕ) (acc : ℤ) : acc ≤ maxExceptFrom xs i c acc := by
  induction xs generalizing i acc with
  | nil => exact le_refl _
  | cons x xs ih =>
    simp only [TransformerCore.maxExceptFrom]
    split_ifs
    · exact ih _ _
    · refine le_trans ?_ (ih _ _)
      rw [maxI_eq_max]; exact le_max_left _ _

theorem maxExceptFrom_ge (xs : List ℤ) (i c : ℕ) (acc : ℤ) (n : ℕ) (hn : n < xs.length) (hne : i + n ≠ c) :
    nth 0 xs n ≤ maxExceptFrom xs i c acc := by
  induction xs generalizing i acc n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero =>
      have hic : ¬ i = c := by simpa using hne
      simp only [TransformerCore.maxExceptFrom, hic, if_false, nth]
      refine le_trans ?_ (maxExceptFrom_ge_acc _ _ _ _)
      rw [maxI_eq_max]; exact le_max_right _ _
    | succ n =>
      simp only [TransformerCore.maxExceptFrom, nth]
      split_ifs
      · exact ih _ _ _ (by simpa using hn) (by omega)
      · exact ih _ _ _ (by simpa using hn) (by omega)

/-- Every entry of `L` other than the one at `c` is at most `maxExcept L c`. -/
theorem le_maxExcept (L : List ℤ) (c k : ℕ) (hk : k < L.length) (hne : k ≠ c) :
    nth 0 L k ≤ maxExcept L c :=
  maxExceptFrom_ge L 0 c _ k hk (by omega)

theorem logits_length_ge (K : Cfg) (T : Tab) (a b : ℕ) (hCU : T.CU.length = 113) :
    113 ≤ (TransformerCore.logits K T a b).length := by
  simp only [TransformerCore.logits, TransformerCore.length_vadd, TransformerCore.length_smulN, hCU]
  exact le_max_left _ _

/-- **Per pair.** If `tablesOk` holds, the table `G` has 512 rows, and `fastCheck` passes at `(a, b)`, the right logit of
the Mathlib integer program exceeds every other by more than `E2`. -/
theorem hA_of_fastCheck (p : Transformer.ExpParams) (S : ℕ) (T : Tab) (bd : Bnd) (E2 : ℕ)
    (hT : tablesOk T bd = true) (hG : T.G.length = 512) (a b : Fin 113)
    (hf : fastCheck (cfgOf p S) T bd E2 a b = true) :
    ∀ k : Fin 113, k ≠ Transformer.ans a b →
      Transformer.intLogits p (toTables T) S a b k + (E2 : ℤ)
        < Transformer.intLogits p (toTables T) S a b (Transformer.ans a b) := by
  intro k hk
  obtain ⟨_, hmar⟩ := TransformerCore.fastCheck_correct (cfgOf p S) T bd E2 a b a.2 b.2 hT hf
  obtain ⟨_, hCU, _⟩ := TransformerCore.tablesOk_const T bd hT
  rw [TransformerCore.vecOk_iff] at hCU
  have hlen := logits_length_ge (cfgOf p S) T a b hCU.1
  have hc : ((Transformer.ans a b : Fin 113) : ℕ) = (a + b) % 113 := Transformer.ans_val a b
  have hkc : (k : ℕ) ≠ (a + b) % 113 := by
    rw [← hc]; exact fun h => hk (Fin.ext h)
  have hk113 := k.2
  have hle := le_maxExcept (TransformerCore.logits (cfgOf p S) T a b) ((a + b) % 113) k
    (by omega) hkc
  rw [← logits_nth_eq p S T a b hG k, ← logits_nth_eq p S T a b hG (Transformer.ans a b), hc]
  unfold TransformerCore.margin at hmar
  simp only [Int.sub_def, gt_iff_lt] at hmar
  omega

end TransformerBridge

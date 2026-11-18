/- Step 2c: the word-buffer invariant: counter d and registers h1, h2 track the reference word. -/
import lean.Fwd2
import lean.Hash
namespace Lexnet
open Hash
set_option maxHeartbeats 0

theorem code_bd (c : Nat) : 0 ≤ code c ∧ code c ≤ 63 := by
  unfold code; split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem H_nil : H [] = 0 := rfl
theorem H_single (c : Nat) : H [c] = code c := by simp [H]

theorem pow8 : (64 : Int) ^ 7 * 64 = 2 ^ 48 := by decide
theorem H_lt_len (w : List Nat) (v : valid w) (n : Nat) (hn : w.length ≤ n) : H w < 64 ^ n := by
  have h1 := H_lt w v
  have h2 : (64 : Int) ^ w.length ≤ 64 ^ n := by have := Nat.pow_le_pow_right (show 0 < 64 by omega) hn; exact_mod_cast this
  omega

/-- The invariant of the numeric registers against the reference word `w`. -/
def NumInv (ww : Bool) (w : List Nat) (d h1 h2 : Int) : Prop :=
  valid w ∧ w.length ≤ 14 ∧ (0 ≤ d ∧ d ≤ 14) ∧ (0 ≤ h1 ∧ h1 < 2 ^ 48) ∧ (0 ≤ h2 ∧ h2 < 2 ^ 36) ∧
  (ww = true → 1 ≤ w.length ∧ h1 = H (w.take 8) ∧ h2 = H (w.drop 8) ∧
     ((w.length < 14 ∧ d = 15 - w.length) ∨ (w.length = 14 ∧ d ≤ 1))) ∧
  (ww = false → w = [])

def nextWord (ww isW : Bool) (w : List Nat) (c : Nat) : List Nat :=
  if isW then ((if ww then w ++ [c] else [c]).take 14) else []

theorem num_step (ww isW : Bool) (w : List Nat) (c : Nat) (d h1 h2 : Int)
    (inv : NumInv ww w d h1 h2) (hc : isW = true → Ref.isWordChar c = true) :
    NumInv isW (nextWord ww isW w c)
      (hashStep (enc (Ref.isWordChar c)) (code c) (enc ww) d h1 h2).1
      (hashStep (enc (Ref.isWordChar c)) (code c) (enc ww) d h1 h2).2.1
      (hashStep (enc (Ref.isWordChar c)) (code c) (enc ww) d h1 h2).2.2 := by
  obtain ⟨hv, hl, hd, hh1, hh2, hin, hout⟩ := inv
  have cb := code_bd c
  have hHIn : ∀ wcv : Int, (wcv = 0 ∨ wcv = 1) → HIn wcv (code c) d h1 h2 :=
    fun wcv hw => ⟨hw, cb, hd, hh1, hh2⟩
  have hwc : enc (Ref.isWordChar c) = 0 ∨ enc (Ref.isWordChar c) = 1 := by
    cases Ref.isWordChar c <;> simp [enc]
  have hvc : isW = true → valid [c] := fun h x hx => by
    simp at hx; subst hx; exact hc h
  have hbig1 : (64 : Int) ^ 7 = 4398046511104 := by decide
  have lowc : ∀ x : Nat, x ≤ 7 → ((64 : Int) ^ x ≤ 4398046511104) := fun x hx => by
    have := Nat.pow_le_pow_right (show 0 < 64 by omega) hx
    have h2 : (64 : Int) ^ x ≤ 64 ^ 7 := by exact_mod_cast this
    omega
  have e0f : enc false = 0 := rfl
  have e0t : enc true = 1 := rfl
  cases ww
  · -- not in a word
    have := hout rfl; subst this
    obtain ⟨e1, e2, e3⟩ := hash_idle _ _ _ _ _ (hHIn _ hwc)
    rw [e0f]
    cases isW
    · simp only [nextWord, NumInv]
      refine ⟨by simp [valid], by simp, ?_, ?_, ?_, ?_, ?_⟩ <;> first | omega | simp
    · simp only [nextWord, NumInv]
      have hv1 := hvc rfl
      refine ⟨by simpa using hv1, by simp, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · intro _
        refine ⟨by simp, ?_, ?_, Or.inl ⟨by simp, by simp; omega⟩⟩
        · simp [H_single]; omega
        · simp [H_nil]; omega
      · simp
  · rw [e0t]
    obtain ⟨l1, e1, e2, hdl⟩ := hin rfl
    have hcls : ∀ wcv : Int, enc (Ref.isWordChar c) = wcv → isW = true → wcv = 1 := by
      intro wcv h hw; have := hc hw; rw [this] at h; simp [enc] at h; omega
    rcases hdl with ⟨l2, e3⟩ | ⟨l2, e3⟩
    · by_cases hlen7 : w.length ≤ 7
      · obtain ⟨a1, a2, a3, a4⟩ := hash_first _ _ _ _ _ (hHIn _ hwc) (by omega)
        have tk : w.take 8 = w := List.take_of_length_le (by omega)
        have dr : w.drop 8 = [] := List.drop_of_length_le (by omega)
        have hlt : H w < 4398046511104 := by
          have := H_lt_len w hv 7 hlen7; omega
        rw [tk] at e1; rw [dr, H_nil] at e2
        cases isW
        · simp only [nextWord, NumInv]
          refine ⟨by simp [valid], by simp, ?_, ?_, ?_, ?_, ?_⟩
          · omega
          · rcases hwc with h | h
            · have := a3 h; omega
            · have := a2 h; omega
          · omega
          · simp
          · simp
        · simp only [nextWord, NumInv, if_true]
          have hw1 := hcls _ rfl rfl
          have hv1 := hvc rfl
          have tk2 : (w ++ [c]).take 14 = w ++ [c] := List.take_of_length_le (by simp; omega)
          have tk3 : (w ++ [c]).take 8 = w ++ [c] := List.take_of_length_le (by simp; omega)
          have dr3 : (w ++ [c]).drop 8 = [] := List.drop_of_length_le (by simp; omega)
          rw [tk2]
          have a2' := a2 hw1
          refine ⟨?_, by simp; omega, ?_, ?_, ?_, ?_, ?_⟩
          · intro x hx; simp at hx; rcases hx with hx | hx
            · exact hv x hx
            · subst hx; exact hc rfl
          · omega
          · rw [a2']; have := code_bd c; omega
          · omega
          · intro _
            refine ⟨by simp, ?_, ?_, Or.inl ⟨by simp; omega, by simp; omega⟩⟩
            · rw [tk3, H_snoc, a2']; omega
            · rw [dr3, H_nil]; omega
          · simp
      · -- 8 ≤ length ≤ 13
        obtain ⟨a1, a2, a3, a4⟩ := hash_second _ _ _ _ _ (hHIn _ hwc) (by omega) (by omega)
        have hlt : H (w.drop 8) < 1073741824 := by
          have := H_lt_len (w.drop 8) (fun x hx => hv x (List.mem_of_mem_drop hx)) 5 (by simp; omega)
          have e : (64 : Int) ^ 5 = 1073741824 := by decide
          omega
        cases isW
        · simp only [nextWord, NumInv]
          refine ⟨by simp [valid], by simp, ?_, ?_, ?_, ?_, ?_⟩
          · omega
          · omega
          · rcases hwc with h | h
            · have := a4 h; have := code_bd c; omega
            · have := a3 h; have := code_bd c; omega
          · simp
          · simp
        · simp only [nextWord, NumInv, if_true]
          have hw1 := hcls _ rfl rfl
          have tk2 : (w ++ [c]).take 14 = w ++ [c] := List.take_of_length_le (by simp; omega)
          have tk3 : (w ++ [c]).take 8 = w.take 8 := by
            rw [List.take_append]; simp [Nat.sub_eq_zero_of_le (show 8 ≤ w.length by omega)]
          have dr3 : (w ++ [c]).drop 8 = w.drop 8 ++ [c] := by
            rw [List.drop_append]; simp [Nat.sub_eq_zero_of_le (show 8 ≤ w.length by omega)]
          rw [tk2]
          have a3' := a3 hw1
          have cb' := code_bd c
          refine ⟨?_, by simp; omega, ?_, ?_, ?_, ?_, ?_⟩
          · intro x hx; simp at hx; rcases hx with hx | hx
            · exact hv x hx
            · subst hx; exact hc rfl
          · omega
          · omega
          · omega
          · intro _
            refine ⟨by simp, ?_, ?_, ?_⟩
            · rw [tk3, a2]; exact e1
            · rw [dr3, H_snoc, a3', e2]
            · simp only [List.length_append, List.length_singleton]; omega
          · simp
    · -- length 14, counter exhausted
      obtain ⟨a1, a2, a3⟩ := hash_full _ _ _ _ _ (hHIn _ hwc) e3
      cases isW
      · simp only [nextWord, NumInv]
        refine ⟨by simp [valid], by simp, ?_, ?_, ?_, ?_, ?_⟩ <;> first | omega | simp
      · simp only [nextWord, NumInv, if_true]
        have tk2 : (w ++ [c]).take 14 = w := by
          rw [List.take_append]; simp [Nat.sub_eq_zero_of_le (show 14 ≤ w.length by omega), List.take_of_length_le (show w.length ≤ 14 by omega)]
        rw [tk2]
        refine ⟨hv, hl, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · omega
        · omega
        · intro _; refine ⟨l1, ?_, ?_, Or.inr ⟨l2, by omega⟩⟩
          · rw [a2]; exact e1
          · rw [a3]; exact e2
        · simp
end Lexnet

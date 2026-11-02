import LeanCheckedNetwork.Seal.C_abs_H512_s1_final.Trained.Table

/-! Rows 88 to 90 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_abs_H512_s1_final.Trained

open LeanCheckedNetwork

theorem fast_88 : ∀ b, b < 97 →
    (fastOkA E1 E2 512 88 b &&
      ((fastAnswerA E1 E2 W2 512 88 b == (88 + b) % 97) == !(wrongRows.getD 88 []).contains b)) = true := by
  decide +kernel

/-- Row 88: the network answers (88 + b) % 97 exactly for the b outside row 88 of `wrongRows`. -/
theorem row_88 : ∀ b, b < 97 → (answer 88 b = (88 + b) % 97 ↔ b ∉ wrongRows.getD 88 []) := by
  intro b hb
  have h := fast_88 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerA E1 E2 W2 88 b = _ ↔ _
  rw [answerA_eq_fastAnswerA E1 E2 W2 512 88 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_89 : ∀ b, b < 97 →
    (fastOkA E1 E2 512 89 b &&
      ((fastAnswerA E1 E2 W2 512 89 b == (89 + b) % 97) == !(wrongRows.getD 89 []).contains b)) = true := by
  decide +kernel

/-- Row 89: the network answers (89 + b) % 97 exactly for the b outside row 89 of `wrongRows`. -/
theorem row_89 : ∀ b, b < 97 → (answer 89 b = (89 + b) % 97 ↔ b ∉ wrongRows.getD 89 []) := by
  intro b hb
  have h := fast_89 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerA E1 E2 W2 89 b = _ ↔ _
  rw [answerA_eq_fastAnswerA E1 E2 W2 512 89 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_90 : ∀ b, b < 97 →
    (fastOkA E1 E2 512 90 b &&
      ((fastAnswerA E1 E2 W2 512 90 b == (90 + b) % 97) == !(wrongRows.getD 90 []).contains b)) = true := by
  decide +kernel

/-- Row 90: the network answers (90 + b) % 97 exactly for the b outside row 90 of `wrongRows`. -/
theorem row_90 : ∀ b, b < 97 → (answer 90 b = (90 + b) % 97 ↔ b ∉ wrongRows.getD 90 []) := by
  intro b hb
  have h := fast_90 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerA E1 E2 W2 90 b = _ ↔ _
  rw [answerA_eq_fastAnswerA E1 E2 W2 512 90 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_abs_H512_s1_final.Trained

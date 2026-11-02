import LeanCheckedNetwork.Seal.C_relu_H512_s1_final.Trained.Table

/-! Rows 79 to 81 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_relu_H512_s1_final.Trained

open LeanCheckedNetwork

theorem fast_79 : ∀ b, b < 97 →
    (fastOkR E1 E2 512 79 b &&
      ((fastAnswerR E1 E2 W2 512 79 b == (79 + b) % 97) == !(wrongRows.getD 79 []).contains b)) = true := by
  decide +kernel

/-- Row 79: the network answers (79 + b) % 97 exactly for the b outside row 79 of `wrongRows`. -/
theorem row_79 : ∀ b, b < 97 → (answer 79 b = (79 + b) % 97 ↔ b ∉ wrongRows.getD 79 []) := by
  intro b hb
  have h := fast_79 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerR E1 E2 W2 79 b = _ ↔ _
  rw [answerR_eq_fastAnswerR E1 E2 W2 512 79 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_80 : ∀ b, b < 97 →
    (fastOkR E1 E2 512 80 b &&
      ((fastAnswerR E1 E2 W2 512 80 b == (80 + b) % 97) == !(wrongRows.getD 80 []).contains b)) = true := by
  decide +kernel

/-- Row 80: the network answers (80 + b) % 97 exactly for the b outside row 80 of `wrongRows`. -/
theorem row_80 : ∀ b, b < 97 → (answer 80 b = (80 + b) % 97 ↔ b ∉ wrongRows.getD 80 []) := by
  intro b hb
  have h := fast_80 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerR E1 E2 W2 80 b = _ ↔ _
  rw [answerR_eq_fastAnswerR E1 E2 W2 512 80 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_81 : ∀ b, b < 97 →
    (fastOkR E1 E2 512 81 b &&
      ((fastAnswerR E1 E2 W2 512 81 b == (81 + b) % 97) == !(wrongRows.getD 81 []).contains b)) = true := by
  decide +kernel

/-- Row 81: the network answers (81 + b) % 97 exactly for the b outside row 81 of `wrongRows`. -/
theorem row_81 : ∀ b, b < 97 → (answer 81 b = (81 + b) % 97 ↔ b ∉ wrongRows.getD 81 []) := by
  intro b hb
  have h := fast_81 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerR E1 E2 W2 81 b = _ ↔ _
  rw [answerR_eq_fastAnswerR E1 E2 W2 512 81 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_relu_H512_s1_final.Trained

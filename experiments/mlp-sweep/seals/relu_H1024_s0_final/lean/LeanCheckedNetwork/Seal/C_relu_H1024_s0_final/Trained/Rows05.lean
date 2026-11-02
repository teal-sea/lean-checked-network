import LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.Trained.Table

/-! Rows 10 to 11 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.Trained

open LeanCheckedNetwork

theorem fast_10 : ∀ b, b < 97 →
    (fastOkR E1 E2 1024 10 b &&
      ((fastAnswerR E1 E2 W2 1024 10 b == (10 + b) % 97) == !(wrongRows.getD 10 []).contains b)) = true := by
  decide +kernel

/-- Row 10: the network answers (10 + b) % 97 exactly for the b outside row 10 of `wrongRows`. -/
theorem row_10 : ∀ b, b < 97 → (answer 10 b = (10 + b) % 97 ↔ b ∉ wrongRows.getD 10 []) := by
  intro b hb
  have h := fast_10 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerR E1 E2 W2 10 b = _ ↔ _
  rw [answerR_eq_fastAnswerR E1 E2 W2 1024 10 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_11 : ∀ b, b < 97 →
    (fastOkR E1 E2 1024 11 b &&
      ((fastAnswerR E1 E2 W2 1024 11 b == (11 + b) % 97) == !(wrongRows.getD 11 []).contains b)) = true := by
  decide +kernel

/-- Row 11: the network answers (11 + b) % 97 exactly for the b outside row 11 of `wrongRows`. -/
theorem row_11 : ∀ b, b < 97 → (answer 11 b = (11 + b) % 97 ↔ b ∉ wrongRows.getD 11 []) := by
  intro b hb
  have h := fast_11 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerR E1 E2 W2 11 b = _ ↔ _
  rw [answerR_eq_fastAnswerR E1 E2 W2 1024 11 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.Trained

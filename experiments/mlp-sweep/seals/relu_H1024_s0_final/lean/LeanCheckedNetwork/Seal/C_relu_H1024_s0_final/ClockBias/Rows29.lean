import LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.ClockBias.Table

/-! Rows 58 to 59 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.ClockBias

open LeanCheckedNetwork

theorem fast_58 : ∀ b, b < 97 →
    (fastOkR E1 E2 1024 58 b &&
      ((fastAnswerR E1 E2 W2 1024 58 b == (58 + b) % 97) == !(wrongRows.getD 58 []).contains b)) = true := by
  decide +kernel

/-- Row 58: the network answers (58 + b) % 97 exactly for the b outside row 58 of `wrongRows`. -/
theorem row_58 : ∀ b, b < 97 → (answer 58 b = (58 + b) % 97 ↔ b ∉ wrongRows.getD 58 []) := by
  intro b hb
  have h := fast_58 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerR E1 E2 W2 58 b = _ ↔ _
  rw [answerR_eq_fastAnswerR E1 E2 W2 1024 58 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_59 : ∀ b, b < 97 →
    (fastOkR E1 E2 1024 59 b &&
      ((fastAnswerR E1 E2 W2 1024 59 b == (59 + b) % 97) == !(wrongRows.getD 59 []).contains b)) = true := by
  decide +kernel

/-- Row 59: the network answers (59 + b) % 97 exactly for the b outside row 59 of `wrongRows`. -/
theorem row_59 : ∀ b, b < 97 → (answer 59 b = (59 + b) % 97 ↔ b ∉ wrongRows.getD 59 []) := by
  intro b hb
  have h := fast_59 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerR E1 E2 W2 59 b = _ ↔ _
  rw [answerR_eq_fastAnswerR E1 E2 W2 1024 59 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.ClockBias

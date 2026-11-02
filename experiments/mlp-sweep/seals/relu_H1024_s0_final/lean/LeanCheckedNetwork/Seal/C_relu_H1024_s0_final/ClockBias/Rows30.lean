import LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.ClockBias.Table

/-! Rows 60 to 61 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.ClockBias

open LeanCheckedNetwork

theorem fast_60 : ∀ b, b < 97 →
    (fastOkR E1 E2 1024 60 b &&
      ((fastAnswerR E1 E2 W2 1024 60 b == (60 + b) % 97) == !(wrongRows.getD 60 []).contains b)) = true := by
  decide +kernel

/-- Row 60: the network answers (60 + b) % 97 exactly for the b outside row 60 of `wrongRows`. -/
theorem row_60 : ∀ b, b < 97 → (answer 60 b = (60 + b) % 97 ↔ b ∉ wrongRows.getD 60 []) := by
  intro b hb
  have h := fast_60 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerR E1 E2 W2 60 b = _ ↔ _
  rw [answerR_eq_fastAnswerR E1 E2 W2 1024 60 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_61 : ∀ b, b < 97 →
    (fastOkR E1 E2 1024 61 b &&
      ((fastAnswerR E1 E2 W2 1024 61 b == (61 + b) % 97) == !(wrongRows.getD 61 []).contains b)) = true := by
  decide +kernel

/-- Row 61: the network answers (61 + b) % 97 exactly for the b outside row 61 of `wrongRows`. -/
theorem row_61 : ∀ b, b < 97 → (answer 61 b = (61 + b) % 97 ↔ b ∉ wrongRows.getD 61 []) := by
  intro b hb
  have h := fast_61 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerR E1 E2 W2 61 b = _ ↔ _
  rw [answerR_eq_fastAnswerR E1 E2 W2 1024 61 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.ClockBias

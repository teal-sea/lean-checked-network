import LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.ClockBias.Table

/-! Rows 95 to 95 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.ClockBias

open LeanCheckedNetwork

theorem fast_95 : ∀ b, b < 97 →
    (fastOkR E1 E2 1024 95 b &&
      ((fastAnswerR E1 E2 W2 1024 95 b == (95 + b) % 97) == !(wrongRows.getD 95 []).contains b)) = true := by
  decide +kernel

/-- Row 95: the network answers (95 + b) % 97 exactly for the b outside row 95 of `wrongRows`. -/
theorem row_95 : ∀ b, b < 97 → (answer 95 b = (95 + b) % 97 ↔ b ∉ wrongRows.getD 95 []) := by
  intro b hb
  have h := fast_95 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerR E1 E2 W2 95 b = _ ↔ _
  rw [answerR_eq_fastAnswerR E1 E2 W2 1024 95 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.ClockBias

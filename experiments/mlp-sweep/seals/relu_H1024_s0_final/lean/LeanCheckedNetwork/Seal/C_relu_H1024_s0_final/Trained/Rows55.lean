import LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.Trained.Table

/-! Rows 88 to 88 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.Trained

open LeanCheckedNetwork

theorem fast_88 : ∀ b, b < 97 →
    (fastOkR E1 E2 1024 88 b &&
      ((fastAnswerR E1 E2 W2 1024 88 b == (88 + b) % 97) == !(wrongRows.getD 88 []).contains b)) = true := by
  decide +kernel

/-- Row 88: the network answers (88 + b) % 97 exactly for the b outside row 88 of `wrongRows`. -/
theorem row_88 : ∀ b, b < 97 → (answer 88 b = (88 + b) % 97 ↔ b ∉ wrongRows.getD 88 []) := by
  intro b hb
  have h := fast_88 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerR E1 E2 W2 88 b = _ ↔ _
  rw [answerR_eq_fastAnswerR E1 E2 W2 1024 88 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.Trained

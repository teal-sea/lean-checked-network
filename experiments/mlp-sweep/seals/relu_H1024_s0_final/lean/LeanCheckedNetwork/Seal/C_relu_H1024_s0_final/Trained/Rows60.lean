import LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.Trained.Table

/-! Rows 93 to 93 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.Trained

open LeanCheckedNetwork

theorem fast_93 : ∀ b, b < 97 →
    (fastOkR E1 E2 1024 93 b &&
      ((fastAnswerR E1 E2 W2 1024 93 b == (93 + b) % 97) == !(wrongRows.getD 93 []).contains b)) = true := by
  decide +kernel

/-- Row 93: the network answers (93 + b) % 97 exactly for the b outside row 93 of `wrongRows`. -/
theorem row_93 : ∀ b, b < 97 → (answer 93 b = (93 + b) % 97 ↔ b ∉ wrongRows.getD 93 []) := by
  intro b hb
  have h := fast_93 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerR E1 E2 W2 93 b = _ ↔ _
  rw [answerR_eq_fastAnswerR E1 E2 W2 1024 93 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_relu_H1024_s0_final.Trained

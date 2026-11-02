import LeanCheckedNetwork.Seal.C_x2_H1024_s2_step1.Trained.Table

/-! Rows 72 to 72 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H1024_s2_step1.Trained

open LeanCheckedNetwork

theorem fast_72 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 72 b &&
      ((fastAnswer E1 E2 W2 1024 72 b == (72 + b) % 97) == !(wrongRows.getD 72 []).contains b)) = true := by
  decide +kernel

/-- Row 72: the network answers (72 + b) % 97 exactly for the b outside row 72 of `wrongRows`. -/
theorem row_72 : ∀ b, b < 97 → (answer 72 b = (72 + b) % 97 ↔ b ∉ wrongRows.getD 72 []) := by
  intro b hb
  have h := fast_72 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 72 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 72 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H1024_s2_step1.Trained

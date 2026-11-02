import LeanCheckedNetwork.Seal.C_x2_H1024_s1_step1.Trained.Table

/-! Rows 79 to 79 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H1024_s1_step1.Trained

open LeanCheckedNetwork

theorem fast_79 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 79 b &&
      ((fastAnswer E1 E2 W2 1024 79 b == (79 + b) % 97) == !(wrongRows.getD 79 []).contains b)) = true := by
  decide +kernel

/-- Row 79: the network answers (79 + b) % 97 exactly for the b outside row 79 of `wrongRows`. -/
theorem row_79 : ∀ b, b < 97 → (answer 79 b = (79 + b) % 97 ↔ b ∉ wrongRows.getD 79 []) := by
  intro b hb
  have h := fast_79 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 79 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 79 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H1024_s1_step1.Trained

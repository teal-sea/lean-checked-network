import LeanCheckedNetwork.Seal.C_x2_H1024_s2_step1.Trained.Table

/-! Rows 80 to 80 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H1024_s2_step1.Trained

open LeanCheckedNetwork

theorem fast_80 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 80 b &&
      ((fastAnswer E1 E2 W2 1024 80 b == (80 + b) % 97) == !(wrongRows.getD 80 []).contains b)) = true := by
  decide +kernel

/-- Row 80: the network answers (80 + b) % 97 exactly for the b outside row 80 of `wrongRows`. -/
theorem row_80 : ∀ b, b < 97 → (answer 80 b = (80 + b) % 97 ↔ b ∉ wrongRows.getD 80 []) := by
  intro b hb
  have h := fast_80 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 80 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 80 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H1024_s2_step1.Trained

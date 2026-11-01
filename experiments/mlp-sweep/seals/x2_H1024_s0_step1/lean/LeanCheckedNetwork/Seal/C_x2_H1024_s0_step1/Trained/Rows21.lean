import LeanCheckedNetwork.Seal.C_x2_H1024_s0_step1.Trained.Table

/-! Rows 42 to 43 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H1024_s0_step1.Trained

open LeanCheckedNetwork

theorem fast_42 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 42 b &&
      ((fastAnswer E1 E2 W2 1024 42 b == (42 + b) % 97) == !(wrongRows.getD 42 []).contains b)) = true := by
  decide +kernel

/-- Row 42: the network answers (42 + b) % 97 exactly for the b outside row 42 of `wrongRows`. -/
theorem row_42 : ∀ b, b < 97 → (answer 42 b = (42 + b) % 97 ↔ b ∉ wrongRows.getD 42 []) := by
  intro b hb
  have h := fast_42 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 42 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 42 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_43 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 43 b &&
      ((fastAnswer E1 E2 W2 1024 43 b == (43 + b) % 97) == !(wrongRows.getD 43 []).contains b)) = true := by
  decide +kernel

/-- Row 43: the network answers (43 + b) % 97 exactly for the b outside row 43 of `wrongRows`. -/
theorem row_43 : ∀ b, b < 97 → (answer 43 b = (43 + b) % 97 ↔ b ∉ wrongRows.getD 43 []) := by
  intro b hb
  have h := fast_43 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 43 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 43 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H1024_s0_step1.Trained

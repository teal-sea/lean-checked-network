import LeanCheckedNetwork.Seal.C_x2_H1024_s1_step1.Trained.Table

/-! Rows 34 to 35 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H1024_s1_step1.Trained

open LeanCheckedNetwork

theorem fast_34 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 34 b &&
      ((fastAnswer E1 E2 W2 1024 34 b == (34 + b) % 97) == !(wrongRows.getD 34 []).contains b)) = true := by
  decide +kernel

/-- Row 34: the network answers (34 + b) % 97 exactly for the b outside row 34 of `wrongRows`. -/
theorem row_34 : ∀ b, b < 97 → (answer 34 b = (34 + b) % 97 ↔ b ∉ wrongRows.getD 34 []) := by
  intro b hb
  have h := fast_34 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 34 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 34 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_35 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 35 b &&
      ((fastAnswer E1 E2 W2 1024 35 b == (35 + b) % 97) == !(wrongRows.getD 35 []).contains b)) = true := by
  decide +kernel

/-- Row 35: the network answers (35 + b) % 97 exactly for the b outside row 35 of `wrongRows`. -/
theorem row_35 : ∀ b, b < 97 → (answer 35 b = (35 + b) % 97 ↔ b ∉ wrongRows.getD 35 []) := by
  intro b hb
  have h := fast_35 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 35 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 35 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H1024_s1_step1.Trained

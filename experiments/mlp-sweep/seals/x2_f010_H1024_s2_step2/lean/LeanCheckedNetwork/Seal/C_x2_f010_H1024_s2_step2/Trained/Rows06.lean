import LeanCheckedNetwork.Seal.C_x2_f010_H1024_s2_step2.Trained.Table

/-! Rows 12 to 13 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_f010_H1024_s2_step2.Trained

open LeanCheckedNetwork

theorem fast_12 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 12 b &&
      ((fastAnswer E1 E2 W2 1024 12 b == (12 + b) % 97) == !(wrongRows.getD 12 []).contains b)) = true := by
  decide +kernel

/-- Row 12: the network answers (12 + b) % 97 exactly for the b outside row 12 of `wrongRows`. -/
theorem row_12 : ∀ b, b < 97 → (answer 12 b = (12 + b) % 97 ↔ b ∉ wrongRows.getD 12 []) := by
  intro b hb
  have h := fast_12 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 12 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 12 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_13 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 13 b &&
      ((fastAnswer E1 E2 W2 1024 13 b == (13 + b) % 97) == !(wrongRows.getD 13 []).contains b)) = true := by
  decide +kernel

/-- Row 13: the network answers (13 + b) % 97 exactly for the b outside row 13 of `wrongRows`. -/
theorem row_13 : ∀ b, b < 97 → (answer 13 b = (13 + b) % 97 ↔ b ∉ wrongRows.getD 13 []) := by
  intro b hb
  have h := fast_13 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 13 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 13 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_f010_H1024_s2_step2.Trained

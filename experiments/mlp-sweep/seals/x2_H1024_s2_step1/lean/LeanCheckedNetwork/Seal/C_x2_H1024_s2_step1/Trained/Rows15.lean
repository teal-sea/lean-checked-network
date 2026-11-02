import LeanCheckedNetwork.Seal.C_x2_H1024_s2_step1.Trained.Table

/-! Rows 30 to 31 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H1024_s2_step1.Trained

open LeanCheckedNetwork

theorem fast_30 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 30 b &&
      ((fastAnswer E1 E2 W2 1024 30 b == (30 + b) % 97) == !(wrongRows.getD 30 []).contains b)) = true := by
  decide +kernel

/-- Row 30: the network answers (30 + b) % 97 exactly for the b outside row 30 of `wrongRows`. -/
theorem row_30 : ∀ b, b < 97 → (answer 30 b = (30 + b) % 97 ↔ b ∉ wrongRows.getD 30 []) := by
  intro b hb
  have h := fast_30 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 30 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 30 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_31 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 31 b &&
      ((fastAnswer E1 E2 W2 1024 31 b == (31 + b) % 97) == !(wrongRows.getD 31 []).contains b)) = true := by
  decide +kernel

/-- Row 31: the network answers (31 + b) % 97 exactly for the b outside row 31 of `wrongRows`. -/
theorem row_31 : ∀ b, b < 97 → (answer 31 b = (31 + b) % 97 ↔ b ∉ wrongRows.getD 31 []) := by
  intro b hb
  have h := fast_31 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 31 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 31 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H1024_s2_step1.Trained

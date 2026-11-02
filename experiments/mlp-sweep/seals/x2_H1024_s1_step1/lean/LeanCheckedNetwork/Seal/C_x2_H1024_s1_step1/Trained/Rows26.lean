import LeanCheckedNetwork.Seal.C_x2_H1024_s1_step1.Trained.Table

/-! Rows 52 to 53 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H1024_s1_step1.Trained

open LeanCheckedNetwork

theorem fast_52 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 52 b &&
      ((fastAnswer E1 E2 W2 1024 52 b == (52 + b) % 97) == !(wrongRows.getD 52 []).contains b)) = true := by
  decide +kernel

/-- Row 52: the network answers (52 + b) % 97 exactly for the b outside row 52 of `wrongRows`. -/
theorem row_52 : ∀ b, b < 97 → (answer 52 b = (52 + b) % 97 ↔ b ∉ wrongRows.getD 52 []) := by
  intro b hb
  have h := fast_52 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 52 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 52 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_53 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 53 b &&
      ((fastAnswer E1 E2 W2 1024 53 b == (53 + b) % 97) == !(wrongRows.getD 53 []).contains b)) = true := by
  decide +kernel

/-- Row 53: the network answers (53 + b) % 97 exactly for the b outside row 53 of `wrongRows`. -/
theorem row_53 : ∀ b, b < 97 → (answer 53 b = (53 + b) % 97 ↔ b ∉ wrongRows.getD 53 []) := by
  intro b hb
  have h := fast_53 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 53 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 53 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H1024_s1_step1.Trained

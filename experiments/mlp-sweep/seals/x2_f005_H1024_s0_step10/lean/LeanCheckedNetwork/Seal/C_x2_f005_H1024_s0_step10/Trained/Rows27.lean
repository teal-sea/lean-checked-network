import LeanCheckedNetwork.Seal.C_x2_f005_H1024_s0_step10.Trained.Table

/-! Rows 54 to 55 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_f005_H1024_s0_step10.Trained

open LeanCheckedNetwork

theorem fast_54 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 54 b &&
      ((fastAnswer E1 E2 W2 1024 54 b == (54 + b) % 97) == !(wrongRows.getD 54 []).contains b)) = true := by
  decide +kernel

/-- Row 54: the network answers (54 + b) % 97 exactly for the b outside row 54 of `wrongRows`. -/
theorem row_54 : ∀ b, b < 97 → (answer 54 b = (54 + b) % 97 ↔ b ∉ wrongRows.getD 54 []) := by
  intro b hb
  have h := fast_54 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 54 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 54 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_55 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 55 b &&
      ((fastAnswer E1 E2 W2 1024 55 b == (55 + b) % 97) == !(wrongRows.getD 55 []).contains b)) = true := by
  decide +kernel

/-- Row 55: the network answers (55 + b) % 97 exactly for the b outside row 55 of `wrongRows`. -/
theorem row_55 : ∀ b, b < 97 → (answer 55 b = (55 + b) % 97 ↔ b ∉ wrongRows.getD 55 []) := by
  intro b hb
  have h := fast_55 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 55 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 55 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_f005_H1024_s0_step10.Trained

import LeanCheckedNetwork.Seal.C_x2_ht70_H1024_s0_step15.ClockBias.Table

/-! Rows 6 to 7 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_ht70_H1024_s0_step15.ClockBias

open LeanCheckedNetwork

theorem fast_6 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 6 b &&
      ((fastAnswer E1 E2 W2 1024 6 b == (6 + b) % 97) == !(wrongRows.getD 6 []).contains b)) = true := by
  decide +kernel

/-- Row 6: the network answers (6 + b) % 97 exactly for the b outside row 6 of `wrongRows`. -/
theorem row_6 : ∀ b, b < 97 → (answer 6 b = (6 + b) % 97 ↔ b ∉ wrongRows.getD 6 []) := by
  intro b hb
  have h := fast_6 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 6 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 6 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_7 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 7 b &&
      ((fastAnswer E1 E2 W2 1024 7 b == (7 + b) % 97) == !(wrongRows.getD 7 []).contains b)) = true := by
  decide +kernel

/-- Row 7: the network answers (7 + b) % 97 exactly for the b outside row 7 of `wrongRows`. -/
theorem row_7 : ∀ b, b < 97 → (answer 7 b = (7 + b) % 97 ↔ b ∉ wrongRows.getD 7 []) := by
  intro b hb
  have h := fast_7 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 7 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 7 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_ht70_H1024_s0_step15.ClockBias

import LeanCheckedNetwork.Seal.C_x2_ht70_H1024_s0_step15.ClockBias.Table

/-! Rows 24 to 25 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_ht70_H1024_s0_step15.ClockBias

open LeanCheckedNetwork

theorem fast_24 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 24 b &&
      ((fastAnswer E1 E2 W2 1024 24 b == (24 + b) % 97) == !(wrongRows.getD 24 []).contains b)) = true := by
  decide +kernel

/-- Row 24: the network answers (24 + b) % 97 exactly for the b outside row 24 of `wrongRows`. -/
theorem row_24 : ∀ b, b < 97 → (answer 24 b = (24 + b) % 97 ↔ b ∉ wrongRows.getD 24 []) := by
  intro b hb
  have h := fast_24 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 24 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 24 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_25 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 25 b &&
      ((fastAnswer E1 E2 W2 1024 25 b == (25 + b) % 97) == !(wrongRows.getD 25 []).contains b)) = true := by
  decide +kernel

/-- Row 25: the network answers (25 + b) % 97 exactly for the b outside row 25 of `wrongRows`. -/
theorem row_25 : ∀ b, b < 97 → (answer 25 b = (25 + b) % 97 ↔ b ∉ wrongRows.getD 25 []) := by
  intro b hb
  have h := fast_25 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 25 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 25 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_ht70_H1024_s0_step15.ClockBias

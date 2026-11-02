import LeanCheckedNetwork.Seal.C_x2_ht30_H1024_s0_step2.ClockBias.Table

/-! Rows 20 to 21 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_ht30_H1024_s0_step2.ClockBias

open LeanCheckedNetwork

theorem fast_20 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 20 b &&
      ((fastAnswer E1 E2 W2 1024 20 b == (20 + b) % 97) == !(wrongRows.getD 20 []).contains b)) = true := by
  decide +kernel

/-- Row 20: the network answers (20 + b) % 97 exactly for the b outside row 20 of `wrongRows`. -/
theorem row_20 : ∀ b, b < 97 → (answer 20 b = (20 + b) % 97 ↔ b ∉ wrongRows.getD 20 []) := by
  intro b hb
  have h := fast_20 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 20 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 20 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_21 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 21 b &&
      ((fastAnswer E1 E2 W2 1024 21 b == (21 + b) % 97) == !(wrongRows.getD 21 []).contains b)) = true := by
  decide +kernel

/-- Row 21: the network answers (21 + b) % 97 exactly for the b outside row 21 of `wrongRows`. -/
theorem row_21 : ∀ b, b < 97 → (answer 21 b = (21 + b) % 97 ↔ b ∉ wrongRows.getD 21 []) := by
  intro b hb
  have h := fast_21 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 21 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 21 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_ht30_H1024_s0_step2.ClockBias

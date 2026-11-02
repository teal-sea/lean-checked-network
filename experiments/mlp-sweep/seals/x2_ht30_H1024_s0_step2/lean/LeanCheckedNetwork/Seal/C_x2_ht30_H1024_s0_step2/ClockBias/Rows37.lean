import LeanCheckedNetwork.Seal.C_x2_ht30_H1024_s0_step2.ClockBias.Table

/-! Rows 70 to 70 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_ht30_H1024_s0_step2.ClockBias

open LeanCheckedNetwork

theorem fast_70 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 70 b &&
      ((fastAnswer E1 E2 W2 1024 70 b == (70 + b) % 97) == !(wrongRows.getD 70 []).contains b)) = true := by
  decide +kernel

/-- Row 70: the network answers (70 + b) % 97 exactly for the b outside row 70 of `wrongRows`. -/
theorem row_70 : ∀ b, b < 97 → (answer 70 b = (70 + b) % 97 ↔ b ∉ wrongRows.getD 70 []) := by
  intro b hb
  have h := fast_70 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 70 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 70 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_ht30_H1024_s0_step2.ClockBias

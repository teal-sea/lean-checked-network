import LeanCheckedNetwork.Seal.C_x2_H1024_s0_step1.ClockBias.Table

/-! Rows 89 to 89 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H1024_s0_step1.ClockBias

open LeanCheckedNetwork

theorem fast_89 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 89 b &&
      ((fastAnswer E1 E2 W2 1024 89 b == (89 + b) % 97) == !(wrongRows.getD 89 []).contains b)) = true := by
  decide +kernel

/-- Row 89: the network answers (89 + b) % 97 exactly for the b outside row 89 of `wrongRows`. -/
theorem row_89 : ∀ b, b < 97 → (answer 89 b = (89 + b) % 97 ↔ b ∉ wrongRows.getD 89 []) := by
  intro b hb
  have h := fast_89 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 89 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 89 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H1024_s0_step1.ClockBias

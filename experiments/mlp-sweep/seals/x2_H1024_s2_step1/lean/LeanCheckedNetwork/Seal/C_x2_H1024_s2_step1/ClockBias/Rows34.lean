import LeanCheckedNetwork.Seal.C_x2_H1024_s2_step1.ClockBias.Table

/-! Rows 67 to 67 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H1024_s2_step1.ClockBias

open LeanCheckedNetwork

theorem fast_67 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 67 b &&
      ((fastAnswer E1 E2 W2 1024 67 b == (67 + b) % 97) == !(wrongRows.getD 67 []).contains b)) = true := by
  decide +kernel

/-- Row 67: the network answers (67 + b) % 97 exactly for the b outside row 67 of `wrongRows`. -/
theorem row_67 : ∀ b, b < 97 → (answer 67 b = (67 + b) % 97 ↔ b ∉ wrongRows.getD 67 []) := by
  intro b hb
  have h := fast_67 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 67 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 67 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H1024_s2_step1.ClockBias

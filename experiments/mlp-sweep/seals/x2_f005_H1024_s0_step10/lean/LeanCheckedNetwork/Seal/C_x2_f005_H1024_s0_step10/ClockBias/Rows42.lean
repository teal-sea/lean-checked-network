import LeanCheckedNetwork.Seal.C_x2_f005_H1024_s0_step10.ClockBias.Table

/-! Rows 75 to 75 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_f005_H1024_s0_step10.ClockBias

open LeanCheckedNetwork

theorem fast_75 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 75 b &&
      ((fastAnswer E1 E2 W2 1024 75 b == (75 + b) % 97) == !(wrongRows.getD 75 []).contains b)) = true := by
  decide +kernel

/-- Row 75: the network answers (75 + b) % 97 exactly for the b outside row 75 of `wrongRows`. -/
theorem row_75 : ∀ b, b < 97 → (answer 75 b = (75 + b) % 97 ↔ b ∉ wrongRows.getD 75 []) := by
  intro b hb
  have h := fast_75 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 75 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 75 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_f005_H1024_s0_step10.ClockBias

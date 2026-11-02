import LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.ClockBias.Table

/-! Rows 96 to 96 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.ClockBias

open LeanCheckedNetwork

theorem fast_96 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 96 b &&
      ((fastAnswer E1 E2 W2 1024 96 b == (96 + b) % 97) == !(wrongRows.getD 96 []).contains b)) = true := by
  decide +kernel

/-- Row 96: the network answers (96 + b) % 97 exactly for the b outside row 96 of `wrongRows`. -/
theorem row_96 : ∀ b, b < 97 → (answer 96 b = (96 + b) % 97 ↔ b ∉ wrongRows.getD 96 []) := by
  intro b hb
  have h := fast_96 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 96 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 96 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.ClockBias

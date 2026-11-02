import LeanCheckedNetwork.Seal.C_x2_f005_H1024_s0_step10.ClockBias.Table

/-! Rows 92 to 92 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_f005_H1024_s0_step10.ClockBias

open LeanCheckedNetwork

theorem fast_92 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 92 b &&
      ((fastAnswer E1 E2 W2 1024 92 b == (92 + b) % 97) == !(wrongRows.getD 92 []).contains b)) = true := by
  decide +kernel

/-- Row 92: the network answers (92 + b) % 97 exactly for the b outside row 92 of `wrongRows`. -/
theorem row_92 : ∀ b, b < 97 → (answer 92 b = (92 + b) % 97 ↔ b ∉ wrongRows.getD 92 []) := by
  intro b hb
  have h := fast_92 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 92 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 92 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_f005_H1024_s0_step10.ClockBias

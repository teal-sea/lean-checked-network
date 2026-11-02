import LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.ClockBias.Table

/-! Rows 73 to 73 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.ClockBias

open LeanCheckedNetwork

theorem fast_73 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 73 b &&
      ((fastAnswer E1 E2 W2 1024 73 b == (73 + b) % 97) == !(wrongRows.getD 73 []).contains b)) = true := by
  decide +kernel

/-- Row 73: the network answers (73 + b) % 97 exactly for the b outside row 73 of `wrongRows`. -/
theorem row_73 : ∀ b, b < 97 → (answer 73 b = (73 + b) % 97 ↔ b ∉ wrongRows.getD 73 []) := by
  intro b hb
  have h := fast_73 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 73 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 73 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.ClockBias

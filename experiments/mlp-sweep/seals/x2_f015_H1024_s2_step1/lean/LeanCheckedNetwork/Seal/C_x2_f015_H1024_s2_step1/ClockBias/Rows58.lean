import LeanCheckedNetwork.Seal.C_x2_f015_H1024_s2_step1.ClockBias.Table

/-! Rows 91 to 91 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_f015_H1024_s2_step1.ClockBias

open LeanCheckedNetwork

theorem fast_91 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 91 b &&
      ((fastAnswer E1 E2 W2 1024 91 b == (91 + b) % 97) == !(wrongRows.getD 91 []).contains b)) = true := by
  decide +kernel

/-- Row 91: the network answers (91 + b) % 97 exactly for the b outside row 91 of `wrongRows`. -/
theorem row_91 : ∀ b, b < 97 → (answer 91 b = (91 + b) % 97 ↔ b ∉ wrongRows.getD 91 []) := by
  intro b hb
  have h := fast_91 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 91 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 91 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_f015_H1024_s2_step1.ClockBias

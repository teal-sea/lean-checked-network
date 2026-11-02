import LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.ClockBias.Table

/-! Rows 14 to 15 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.ClockBias

open LeanCheckedNetwork

theorem fast_14 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 14 b &&
      ((fastAnswer E1 E2 W2 1024 14 b == (14 + b) % 97) == !(wrongRows.getD 14 []).contains b)) = true := by
  decide +kernel

/-- Row 14: the network answers (14 + b) % 97 exactly for the b outside row 14 of `wrongRows`. -/
theorem row_14 : ∀ b, b < 97 → (answer 14 b = (14 + b) % 97 ↔ b ∉ wrongRows.getD 14 []) := by
  intro b hb
  have h := fast_14 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 14 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 14 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_15 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 15 b &&
      ((fastAnswer E1 E2 W2 1024 15 b == (15 + b) % 97) == !(wrongRows.getD 15 []).contains b)) = true := by
  decide +kernel

/-- Row 15: the network answers (15 + b) % 97 exactly for the b outside row 15 of `wrongRows`. -/
theorem row_15 : ∀ b, b < 97 → (answer 15 b = (15 + b) % 97 ↔ b ∉ wrongRows.getD 15 []) := by
  intro b hb
  have h := fast_15 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 15 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 15 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.ClockBias

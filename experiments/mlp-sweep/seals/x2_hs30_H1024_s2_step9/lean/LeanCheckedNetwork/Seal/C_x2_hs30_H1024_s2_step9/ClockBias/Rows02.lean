import LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.ClockBias.Table

/-! Rows 4 to 5 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.ClockBias

open LeanCheckedNetwork

theorem fast_4 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 4 b &&
      ((fastAnswer E1 E2 W2 1024 4 b == (4 + b) % 97) == !(wrongRows.getD 4 []).contains b)) = true := by
  decide +kernel

/-- Row 4: the network answers (4 + b) % 97 exactly for the b outside row 4 of `wrongRows`. -/
theorem row_4 : ∀ b, b < 97 → (answer 4 b = (4 + b) % 97 ↔ b ∉ wrongRows.getD 4 []) := by
  intro b hb
  have h := fast_4 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 4 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 4 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_5 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 5 b &&
      ((fastAnswer E1 E2 W2 1024 5 b == (5 + b) % 97) == !(wrongRows.getD 5 []).contains b)) = true := by
  decide +kernel

/-- Row 5: the network answers (5 + b) % 97 exactly for the b outside row 5 of `wrongRows`. -/
theorem row_5 : ∀ b, b < 97 → (answer 5 b = (5 + b) % 97 ↔ b ∉ wrongRows.getD 5 []) := by
  intro b hb
  have h := fast_5 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 5 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 5 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.ClockBias

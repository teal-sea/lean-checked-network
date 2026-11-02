import LeanCheckedNetwork.Seal.C_x2_H512_s0_final.ClockBias.Table

/-! Rows 10 to 12 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H512_s0_final.ClockBias

open LeanCheckedNetwork

theorem fast_10 : ∀ b, b < 97 →
    (fastOk E1 E2 512 10 b &&
      ((fastAnswer E1 E2 W2 512 10 b == (10 + b) % 97) == !(wrongRows.getD 10 []).contains b)) = true := by
  decide +kernel

/-- Row 10: the network answers (10 + b) % 97 exactly for the b outside row 10 of `wrongRows`. -/
theorem row_10 : ∀ b, b < 97 → (answer 10 b = (10 + b) % 97 ↔ b ∉ wrongRows.getD 10 []) := by
  intro b hb
  have h := fast_10 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 10 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 10 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_11 : ∀ b, b < 97 →
    (fastOk E1 E2 512 11 b &&
      ((fastAnswer E1 E2 W2 512 11 b == (11 + b) % 97) == !(wrongRows.getD 11 []).contains b)) = true := by
  decide +kernel

/-- Row 11: the network answers (11 + b) % 97 exactly for the b outside row 11 of `wrongRows`. -/
theorem row_11 : ∀ b, b < 97 → (answer 11 b = (11 + b) % 97 ↔ b ∉ wrongRows.getD 11 []) := by
  intro b hb
  have h := fast_11 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 11 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 11 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_12 : ∀ b, b < 97 →
    (fastOk E1 E2 512 12 b &&
      ((fastAnswer E1 E2 W2 512 12 b == (12 + b) % 97) == !(wrongRows.getD 12 []).contains b)) = true := by
  decide +kernel

/-- Row 12: the network answers (12 + b) % 97 exactly for the b outside row 12 of `wrongRows`. -/
theorem row_12 : ∀ b, b < 97 → (answer 12 b = (12 + b) % 97 ↔ b ∉ wrongRows.getD 12 []) := by
  intro b hb
  have h := fast_12 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 12 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 12 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H512_s0_final.ClockBias

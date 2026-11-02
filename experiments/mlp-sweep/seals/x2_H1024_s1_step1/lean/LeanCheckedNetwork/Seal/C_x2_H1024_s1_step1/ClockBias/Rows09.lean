import LeanCheckedNetwork.Seal.C_x2_H1024_s1_step1.ClockBias.Table

/-! Rows 18 to 19 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H1024_s1_step1.ClockBias

open LeanCheckedNetwork

theorem fast_18 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 18 b &&
      ((fastAnswer E1 E2 W2 1024 18 b == (18 + b) % 97) == !(wrongRows.getD 18 []).contains b)) = true := by
  decide +kernel

/-- Row 18: the network answers (18 + b) % 97 exactly for the b outside row 18 of `wrongRows`. -/
theorem row_18 : ∀ b, b < 97 → (answer 18 b = (18 + b) % 97 ↔ b ∉ wrongRows.getD 18 []) := by
  intro b hb
  have h := fast_18 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 18 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 18 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_19 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 19 b &&
      ((fastAnswer E1 E2 W2 1024 19 b == (19 + b) % 97) == !(wrongRows.getD 19 []).contains b)) = true := by
  decide +kernel

/-- Row 19: the network answers (19 + b) % 97 exactly for the b outside row 19 of `wrongRows`. -/
theorem row_19 : ∀ b, b < 97 → (answer 19 b = (19 + b) % 97 ↔ b ∉ wrongRows.getD 19 []) := by
  intro b hb
  have h := fast_19 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 19 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 19 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H1024_s1_step1.ClockBias

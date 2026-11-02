import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s0_step1.ClockBias.Table

/-! Rows 28 to 30 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H512_lr002_s0_step1.ClockBias

open LeanCheckedNetwork

theorem fast_28 : ∀ b, b < 97 →
    (fastOk E1 E2 512 28 b &&
      ((fastAnswer E1 E2 W2 512 28 b == (28 + b) % 97) == !(wrongRows.getD 28 []).contains b)) = true := by
  decide +kernel

/-- Row 28: the network answers (28 + b) % 97 exactly for the b outside row 28 of `wrongRows`. -/
theorem row_28 : ∀ b, b < 97 → (answer 28 b = (28 + b) % 97 ↔ b ∉ wrongRows.getD 28 []) := by
  intro b hb
  have h := fast_28 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 28 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 28 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_29 : ∀ b, b < 97 →
    (fastOk E1 E2 512 29 b &&
      ((fastAnswer E1 E2 W2 512 29 b == (29 + b) % 97) == !(wrongRows.getD 29 []).contains b)) = true := by
  decide +kernel

/-- Row 29: the network answers (29 + b) % 97 exactly for the b outside row 29 of `wrongRows`. -/
theorem row_29 : ∀ b, b < 97 → (answer 29 b = (29 + b) % 97 ↔ b ∉ wrongRows.getD 29 []) := by
  intro b hb
  have h := fast_29 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 29 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 29 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_30 : ∀ b, b < 97 →
    (fastOk E1 E2 512 30 b &&
      ((fastAnswer E1 E2 W2 512 30 b == (30 + b) % 97) == !(wrongRows.getD 30 []).contains b)) = true := by
  decide +kernel

/-- Row 30: the network answers (30 + b) % 97 exactly for the b outside row 30 of `wrongRows`. -/
theorem row_30 : ∀ b, b < 97 → (answer 30 b = (30 + b) % 97 ↔ b ∉ wrongRows.getD 30 []) := by
  intro b hb
  have h := fast_30 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 30 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 30 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H512_lr002_s0_step1.ClockBias

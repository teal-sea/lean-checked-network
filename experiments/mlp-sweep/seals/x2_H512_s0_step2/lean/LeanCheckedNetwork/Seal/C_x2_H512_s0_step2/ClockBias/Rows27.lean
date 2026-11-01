import LeanCheckedNetwork.Seal.C_x2_H512_s0_step2.ClockBias.Table

/-! Rows 82 to 84 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H512_s0_step2.ClockBias

open LeanCheckedNetwork

theorem fast_82 : ∀ b, b < 97 →
    (fastOk E1 E2 512 82 b &&
      ((fastAnswer E1 E2 W2 512 82 b == (82 + b) % 97) == !(wrongRows.getD 82 []).contains b)) = true := by
  decide +kernel

/-- Row 82: the network answers (82 + b) % 97 exactly for the b outside row 82 of `wrongRows`. -/
theorem row_82 : ∀ b, b < 97 → (answer 82 b = (82 + b) % 97 ↔ b ∉ wrongRows.getD 82 []) := by
  intro b hb
  have h := fast_82 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 82 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 82 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_83 : ∀ b, b < 97 →
    (fastOk E1 E2 512 83 b &&
      ((fastAnswer E1 E2 W2 512 83 b == (83 + b) % 97) == !(wrongRows.getD 83 []).contains b)) = true := by
  decide +kernel

/-- Row 83: the network answers (83 + b) % 97 exactly for the b outside row 83 of `wrongRows`. -/
theorem row_83 : ∀ b, b < 97 → (answer 83 b = (83 + b) % 97 ↔ b ∉ wrongRows.getD 83 []) := by
  intro b hb
  have h := fast_83 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 83 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 83 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_84 : ∀ b, b < 97 →
    (fastOk E1 E2 512 84 b &&
      ((fastAnswer E1 E2 W2 512 84 b == (84 + b) % 97) == !(wrongRows.getD 84 []).contains b)) = true := by
  decide +kernel

/-- Row 84: the network answers (84 + b) % 97 exactly for the b outside row 84 of `wrongRows`. -/
theorem row_84 : ∀ b, b < 97 → (answer 84 b = (84 + b) % 97 ↔ b ∉ wrongRows.getD 84 []) := by
  intro b hb
  have h := fast_84 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 84 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 84 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H512_s0_step2.ClockBias

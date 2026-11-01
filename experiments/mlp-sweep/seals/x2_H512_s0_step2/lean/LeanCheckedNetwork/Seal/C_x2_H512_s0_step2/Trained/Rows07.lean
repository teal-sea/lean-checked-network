import LeanCheckedNetwork.Seal.C_x2_H512_s0_step2.Trained.Table

/-! Rows 22 to 24 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H512_s0_step2.Trained

open LeanCheckedNetwork

theorem fast_22 : ∀ b, b < 97 →
    (fastOk E1 E2 512 22 b &&
      ((fastAnswer E1 E2 W2 512 22 b == (22 + b) % 97) == !(wrongRows.getD 22 []).contains b)) = true := by
  decide +kernel

/-- Row 22: the network answers (22 + b) % 97 exactly for the b outside row 22 of `wrongRows`. -/
theorem row_22 : ∀ b, b < 97 → (answer 22 b = (22 + b) % 97 ↔ b ∉ wrongRows.getD 22 []) := by
  intro b hb
  have h := fast_22 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 22 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 22 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_23 : ∀ b, b < 97 →
    (fastOk E1 E2 512 23 b &&
      ((fastAnswer E1 E2 W2 512 23 b == (23 + b) % 97) == !(wrongRows.getD 23 []).contains b)) = true := by
  decide +kernel

/-- Row 23: the network answers (23 + b) % 97 exactly for the b outside row 23 of `wrongRows`. -/
theorem row_23 : ∀ b, b < 97 → (answer 23 b = (23 + b) % 97 ↔ b ∉ wrongRows.getD 23 []) := by
  intro b hb
  have h := fast_23 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 23 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 23 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_24 : ∀ b, b < 97 →
    (fastOk E1 E2 512 24 b &&
      ((fastAnswer E1 E2 W2 512 24 b == (24 + b) % 97) == !(wrongRows.getD 24 []).contains b)) = true := by
  decide +kernel

/-- Row 24: the network answers (24 + b) % 97 exactly for the b outside row 24 of `wrongRows`. -/
theorem row_24 : ∀ b, b < 97 → (answer 24 b = (24 + b) % 97 ↔ b ∉ wrongRows.getD 24 []) := by
  intro b hb
  have h := fast_24 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 24 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 24 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H512_s0_step2.Trained

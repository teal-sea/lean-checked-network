import LeanCheckedNetwork.Seal.C_x2_H512_s0_step100.Trained.Table

/-! Rows 52 to 54 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H512_s0_step100.Trained

open LeanCheckedNetwork

theorem fast_52 : ∀ b, b < 97 →
    (fastOk E1 E2 512 52 b &&
      ((fastAnswer E1 E2 W2 512 52 b == (52 + b) % 97) == !(wrongRows.getD 52 []).contains b)) = true := by
  decide +kernel

/-- Row 52: the network answers (52 + b) % 97 exactly for the b outside row 52 of `wrongRows`. -/
theorem row_52 : ∀ b, b < 97 → (answer 52 b = (52 + b) % 97 ↔ b ∉ wrongRows.getD 52 []) := by
  intro b hb
  have h := fast_52 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 52 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 52 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_53 : ∀ b, b < 97 →
    (fastOk E1 E2 512 53 b &&
      ((fastAnswer E1 E2 W2 512 53 b == (53 + b) % 97) == !(wrongRows.getD 53 []).contains b)) = true := by
  decide +kernel

/-- Row 53: the network answers (53 + b) % 97 exactly for the b outside row 53 of `wrongRows`. -/
theorem row_53 : ∀ b, b < 97 → (answer 53 b = (53 + b) % 97 ↔ b ∉ wrongRows.getD 53 []) := by
  intro b hb
  have h := fast_53 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 53 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 53 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_54 : ∀ b, b < 97 →
    (fastOk E1 E2 512 54 b &&
      ((fastAnswer E1 E2 W2 512 54 b == (54 + b) % 97) == !(wrongRows.getD 54 []).contains b)) = true := by
  decide +kernel

/-- Row 54: the network answers (54 + b) % 97 exactly for the b outside row 54 of `wrongRows`. -/
theorem row_54 : ∀ b, b < 97 → (answer 54 b = (54 + b) % 97 ↔ b ∉ wrongRows.getD 54 []) := by
  intro b hb
  have h := fast_54 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 54 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 54 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H512_s0_step100.Trained

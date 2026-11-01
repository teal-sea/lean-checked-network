import LeanCheckedNetwork.Seal.C_x2_H512_sgd1536_s1_step1.Trained.Table

/-! Rows 94 to 96 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H512_sgd1536_s1_step1.Trained

open LeanCheckedNetwork

theorem fast_94 : ∀ b, b < 97 →
    (fastOk E1 E2 512 94 b &&
      ((fastAnswer E1 E2 W2 512 94 b == (94 + b) % 97) == !(wrongRows.getD 94 []).contains b)) = true := by
  decide +kernel

/-- Row 94: the network answers (94 + b) % 97 exactly for the b outside row 94 of `wrongRows`. -/
theorem row_94 : ∀ b, b < 97 → (answer 94 b = (94 + b) % 97 ↔ b ∉ wrongRows.getD 94 []) := by
  intro b hb
  have h := fast_94 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 94 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 94 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_95 : ∀ b, b < 97 →
    (fastOk E1 E2 512 95 b &&
      ((fastAnswer E1 E2 W2 512 95 b == (95 + b) % 97) == !(wrongRows.getD 95 []).contains b)) = true := by
  decide +kernel

/-- Row 95: the network answers (95 + b) % 97 exactly for the b outside row 95 of `wrongRows`. -/
theorem row_95 : ∀ b, b < 97 → (answer 95 b = (95 + b) % 97 ↔ b ∉ wrongRows.getD 95 []) := by
  intro b hb
  have h := fast_95 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 95 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 95 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_96 : ∀ b, b < 97 →
    (fastOk E1 E2 512 96 b &&
      ((fastAnswer E1 E2 W2 512 96 b == (96 + b) % 97) == !(wrongRows.getD 96 []).contains b)) = true := by
  decide +kernel

/-- Row 96: the network answers (96 + b) % 97 exactly for the b outside row 96 of `wrongRows`. -/
theorem row_96 : ∀ b, b < 97 → (answer 96 b = (96 + b) % 97 ↔ b ∉ wrongRows.getD 96 []) := by
  intro b hb
  have h := fast_96 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 96 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 96 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H512_sgd1536_s1_step1.Trained

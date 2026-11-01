import LeanCheckedNetwork.Seal.C_x2_H512_s2_final.Trained.Table

/-! Rows 7 to 9 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H512_s2_final.Trained

open LeanCheckedNetwork

theorem fast_7 : ∀ b, b < 97 →
    (fastOk E1 E2 512 7 b &&
      ((fastAnswer E1 E2 W2 512 7 b == (7 + b) % 97) == !(wrongRows.getD 7 []).contains b)) = true := by
  decide +kernel

/-- Row 7: the network answers (7 + b) % 97 exactly for the b outside row 7 of `wrongRows`. -/
theorem row_7 : ∀ b, b < 97 → (answer 7 b = (7 + b) % 97 ↔ b ∉ wrongRows.getD 7 []) := by
  intro b hb
  have h := fast_7 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 7 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 7 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_8 : ∀ b, b < 97 →
    (fastOk E1 E2 512 8 b &&
      ((fastAnswer E1 E2 W2 512 8 b == (8 + b) % 97) == !(wrongRows.getD 8 []).contains b)) = true := by
  decide +kernel

/-- Row 8: the network answers (8 + b) % 97 exactly for the b outside row 8 of `wrongRows`. -/
theorem row_8 : ∀ b, b < 97 → (answer 8 b = (8 + b) % 97 ↔ b ∉ wrongRows.getD 8 []) := by
  intro b hb
  have h := fast_8 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 8 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 8 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_9 : ∀ b, b < 97 →
    (fastOk E1 E2 512 9 b &&
      ((fastAnswer E1 E2 W2 512 9 b == (9 + b) % 97) == !(wrongRows.getD 9 []).contains b)) = true := by
  decide +kernel

/-- Row 9: the network answers (9 + b) % 97 exactly for the b outside row 9 of `wrongRows`. -/
theorem row_9 : ∀ b, b < 97 → (answer 9 b = (9 + b) % 97 ↔ b ∉ wrongRows.getD 9 []) := by
  intro b hb
  have h := fast_9 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 9 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 9 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H512_s2_final.Trained

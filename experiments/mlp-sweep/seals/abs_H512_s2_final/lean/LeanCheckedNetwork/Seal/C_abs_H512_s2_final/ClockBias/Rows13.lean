import LeanCheckedNetwork.Seal.C_abs_H512_s2_final.ClockBias.Table

/-! Rows 40 to 42 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_abs_H512_s2_final.ClockBias

open LeanCheckedNetwork

theorem fast_40 : ∀ b, b < 97 →
    (fastOkA E1 E2 512 40 b &&
      ((fastAnswerA E1 E2 W2 512 40 b == (40 + b) % 97) == !(wrongRows.getD 40 []).contains b)) = true := by
  decide +kernel

/-- Row 40: the network answers (40 + b) % 97 exactly for the b outside row 40 of `wrongRows`. -/
theorem row_40 : ∀ b, b < 97 → (answer 40 b = (40 + b) % 97 ↔ b ∉ wrongRows.getD 40 []) := by
  intro b hb
  have h := fast_40 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerA E1 E2 W2 40 b = _ ↔ _
  rw [answerA_eq_fastAnswerA E1 E2 W2 512 40 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_41 : ∀ b, b < 97 →
    (fastOkA E1 E2 512 41 b &&
      ((fastAnswerA E1 E2 W2 512 41 b == (41 + b) % 97) == !(wrongRows.getD 41 []).contains b)) = true := by
  decide +kernel

/-- Row 41: the network answers (41 + b) % 97 exactly for the b outside row 41 of `wrongRows`. -/
theorem row_41 : ∀ b, b < 97 → (answer 41 b = (41 + b) % 97 ↔ b ∉ wrongRows.getD 41 []) := by
  intro b hb
  have h := fast_41 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerA E1 E2 W2 41 b = _ ↔ _
  rw [answerA_eq_fastAnswerA E1 E2 W2 512 41 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_42 : ∀ b, b < 97 →
    (fastOkA E1 E2 512 42 b &&
      ((fastAnswerA E1 E2 W2 512 42 b == (42 + b) % 97) == !(wrongRows.getD 42 []).contains b)) = true := by
  decide +kernel

/-- Row 42: the network answers (42 + b) % 97 exactly for the b outside row 42 of `wrongRows`. -/
theorem row_42 : ∀ b, b < 97 → (answer 42 b = (42 + b) % 97 ↔ b ∉ wrongRows.getD 42 []) := by
  intro b hb
  have h := fast_42 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerA E1 E2 W2 42 b = _ ↔ _
  rw [answerA_eq_fastAnswerA E1 E2 W2 512 42 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_abs_H512_s2_final.ClockBias

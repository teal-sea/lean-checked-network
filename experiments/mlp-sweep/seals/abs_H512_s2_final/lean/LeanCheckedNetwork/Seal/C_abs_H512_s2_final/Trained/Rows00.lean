import LeanCheckedNetwork.Seal.C_abs_H512_s2_final.Trained.Table

/-! Rows 0 to 3 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_abs_H512_s2_final.Trained

open LeanCheckedNetwork

theorem fast_0 : ∀ b, b < 97 →
    (fastOkA E1 E2 512 0 b &&
      ((fastAnswerA E1 E2 W2 512 0 b == (0 + b) % 97) == !(wrongRows.getD 0 []).contains b)) = true := by
  decide +kernel

/-- Row 0: the network answers (0 + b) % 97 exactly for the b outside row 0 of `wrongRows`. -/
theorem row_0 : ∀ b, b < 97 → (answer 0 b = (0 + b) % 97 ↔ b ∉ wrongRows.getD 0 []) := by
  intro b hb
  have h := fast_0 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerA E1 E2 W2 0 b = _ ↔ _
  rw [answerA_eq_fastAnswerA E1 E2 W2 512 0 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_1 : ∀ b, b < 97 →
    (fastOkA E1 E2 512 1 b &&
      ((fastAnswerA E1 E2 W2 512 1 b == (1 + b) % 97) == !(wrongRows.getD 1 []).contains b)) = true := by
  decide +kernel

/-- Row 1: the network answers (1 + b) % 97 exactly for the b outside row 1 of `wrongRows`. -/
theorem row_1 : ∀ b, b < 97 → (answer 1 b = (1 + b) % 97 ↔ b ∉ wrongRows.getD 1 []) := by
  intro b hb
  have h := fast_1 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerA E1 E2 W2 1 b = _ ↔ _
  rw [answerA_eq_fastAnswerA E1 E2 W2 512 1 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_2 : ∀ b, b < 97 →
    (fastOkA E1 E2 512 2 b &&
      ((fastAnswerA E1 E2 W2 512 2 b == (2 + b) % 97) == !(wrongRows.getD 2 []).contains b)) = true := by
  decide +kernel

/-- Row 2: the network answers (2 + b) % 97 exactly for the b outside row 2 of `wrongRows`. -/
theorem row_2 : ∀ b, b < 97 → (answer 2 b = (2 + b) % 97 ↔ b ∉ wrongRows.getD 2 []) := by
  intro b hb
  have h := fast_2 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerA E1 E2 W2 2 b = _ ↔ _
  rw [answerA_eq_fastAnswerA E1 E2 W2 512 2 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_3 : ∀ b, b < 97 →
    (fastOkA E1 E2 512 3 b &&
      ((fastAnswerA E1 E2 W2 512 3 b == (3 + b) % 97) == !(wrongRows.getD 3 []).contains b)) = true := by
  decide +kernel

/-- Row 3: the network answers (3 + b) % 97 exactly for the b outside row 3 of `wrongRows`. -/
theorem row_3 : ∀ b, b < 97 → (answer 3 b = (3 + b) % 97 ↔ b ∉ wrongRows.getD 3 []) := by
  intro b hb
  have h := fast_3 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answerA E1 E2 W2 3 b = _ ↔ _
  rw [answerA_eq_fastAnswerA E1 E2 W2 512 3 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_abs_H512_s2_final.Trained

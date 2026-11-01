import LeanCheckedNetwork.Seal.C_p97_H128_f0_30_wd0_3_s0.Trained.Table

/-! Rows 7 to 12 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_p97_H128_f0_30_wd0_3_s0.Trained

open LeanCheckedNetwork

theorem fast_7 : ∀ b, b < 97 →
    (fastOk E1 E2 128 7 b &&
      ((fastAnswer E1 E2 W2 128 7 b == (7 + b) % 97) == !(wrongRows.getD 7 []).contains b)) = true := by
  decide +kernel

/-- Row 7: the network answers (7 + b) % 97 exactly for the b outside row 7 of `wrongRows`. -/
theorem row_7 : ∀ b, b < 97 → (answer 7 b = (7 + b) % 97 ↔ b ∉ wrongRows.getD 7 []) := by
  intro b hb
  have h := fast_7 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 7 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 7 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_8 : ∀ b, b < 97 →
    (fastOk E1 E2 128 8 b &&
      ((fastAnswer E1 E2 W2 128 8 b == (8 + b) % 97) == !(wrongRows.getD 8 []).contains b)) = true := by
  decide +kernel

/-- Row 8: the network answers (8 + b) % 97 exactly for the b outside row 8 of `wrongRows`. -/
theorem row_8 : ∀ b, b < 97 → (answer 8 b = (8 + b) % 97 ↔ b ∉ wrongRows.getD 8 []) := by
  intro b hb
  have h := fast_8 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 8 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 8 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_9 : ∀ b, b < 97 →
    (fastOk E1 E2 128 9 b &&
      ((fastAnswer E1 E2 W2 128 9 b == (9 + b) % 97) == !(wrongRows.getD 9 []).contains b)) = true := by
  decide +kernel

/-- Row 9: the network answers (9 + b) % 97 exactly for the b outside row 9 of `wrongRows`. -/
theorem row_9 : ∀ b, b < 97 → (answer 9 b = (9 + b) % 97 ↔ b ∉ wrongRows.getD 9 []) := by
  intro b hb
  have h := fast_9 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 9 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 9 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_10 : ∀ b, b < 97 →
    (fastOk E1 E2 128 10 b &&
      ((fastAnswer E1 E2 W2 128 10 b == (10 + b) % 97) == !(wrongRows.getD 10 []).contains b)) = true := by
  decide +kernel

/-- Row 10: the network answers (10 + b) % 97 exactly for the b outside row 10 of `wrongRows`. -/
theorem row_10 : ∀ b, b < 97 → (answer 10 b = (10 + b) % 97 ↔ b ∉ wrongRows.getD 10 []) := by
  intro b hb
  have h := fast_10 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 10 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 10 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_11 : ∀ b, b < 97 →
    (fastOk E1 E2 128 11 b &&
      ((fastAnswer E1 E2 W2 128 11 b == (11 + b) % 97) == !(wrongRows.getD 11 []).contains b)) = true := by
  decide +kernel

/-- Row 11: the network answers (11 + b) % 97 exactly for the b outside row 11 of `wrongRows`. -/
theorem row_11 : ∀ b, b < 97 → (answer 11 b = (11 + b) % 97 ↔ b ∉ wrongRows.getD 11 []) := by
  intro b hb
  have h := fast_11 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 11 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 11 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_12 : ∀ b, b < 97 →
    (fastOk E1 E2 128 12 b &&
      ((fastAnswer E1 E2 W2 128 12 b == (12 + b) % 97) == !(wrongRows.getD 12 []).contains b)) = true := by
  decide +kernel

/-- Row 12: the network answers (12 + b) % 97 exactly for the b outside row 12 of `wrongRows`. -/
theorem row_12 : ∀ b, b < 97 → (answer 12 b = (12 + b) % 97 ↔ b ∉ wrongRows.getD 12 []) := by
  intro b hb
  have h := fast_12 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 12 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 12 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_p97_H128_f0_30_wd0_3_s0.Trained

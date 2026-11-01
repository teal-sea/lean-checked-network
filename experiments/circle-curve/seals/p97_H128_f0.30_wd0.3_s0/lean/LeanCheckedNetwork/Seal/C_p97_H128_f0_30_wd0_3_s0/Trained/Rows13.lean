import LeanCheckedNetwork.Seal.C_p97_H128_f0_30_wd0_3_s0.Trained.Table

/-! Rows 79 to 84 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_p97_H128_f0_30_wd0_3_s0.Trained

open LeanCheckedNetwork

theorem fast_79 : ∀ b, b < 97 →
    (fastOk E1 E2 128 79 b &&
      ((fastAnswer E1 E2 W2 128 79 b == (79 + b) % 97) == !(wrongRows.getD 79 []).contains b)) = true := by
  decide +kernel

/-- Row 79: the network answers (79 + b) % 97 exactly for the b outside row 79 of `wrongRows`. -/
theorem row_79 : ∀ b, b < 97 → (answer 79 b = (79 + b) % 97 ↔ b ∉ wrongRows.getD 79 []) := by
  intro b hb
  have h := fast_79 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 79 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 79 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_80 : ∀ b, b < 97 →
    (fastOk E1 E2 128 80 b &&
      ((fastAnswer E1 E2 W2 128 80 b == (80 + b) % 97) == !(wrongRows.getD 80 []).contains b)) = true := by
  decide +kernel

/-- Row 80: the network answers (80 + b) % 97 exactly for the b outside row 80 of `wrongRows`. -/
theorem row_80 : ∀ b, b < 97 → (answer 80 b = (80 + b) % 97 ↔ b ∉ wrongRows.getD 80 []) := by
  intro b hb
  have h := fast_80 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 80 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 80 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_81 : ∀ b, b < 97 →
    (fastOk E1 E2 128 81 b &&
      ((fastAnswer E1 E2 W2 128 81 b == (81 + b) % 97) == !(wrongRows.getD 81 []).contains b)) = true := by
  decide +kernel

/-- Row 81: the network answers (81 + b) % 97 exactly for the b outside row 81 of `wrongRows`. -/
theorem row_81 : ∀ b, b < 97 → (answer 81 b = (81 + b) % 97 ↔ b ∉ wrongRows.getD 81 []) := by
  intro b hb
  have h := fast_81 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 81 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 81 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_82 : ∀ b, b < 97 →
    (fastOk E1 E2 128 82 b &&
      ((fastAnswer E1 E2 W2 128 82 b == (82 + b) % 97) == !(wrongRows.getD 82 []).contains b)) = true := by
  decide +kernel

/-- Row 82: the network answers (82 + b) % 97 exactly for the b outside row 82 of `wrongRows`. -/
theorem row_82 : ∀ b, b < 97 → (answer 82 b = (82 + b) % 97 ↔ b ∉ wrongRows.getD 82 []) := by
  intro b hb
  have h := fast_82 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 82 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 82 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_83 : ∀ b, b < 97 →
    (fastOk E1 E2 128 83 b &&
      ((fastAnswer E1 E2 W2 128 83 b == (83 + b) % 97) == !(wrongRows.getD 83 []).contains b)) = true := by
  decide +kernel

/-- Row 83: the network answers (83 + b) % 97 exactly for the b outside row 83 of `wrongRows`. -/
theorem row_83 : ∀ b, b < 97 → (answer 83 b = (83 + b) % 97 ↔ b ∉ wrongRows.getD 83 []) := by
  intro b hb
  have h := fast_83 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 83 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 83 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_84 : ∀ b, b < 97 →
    (fastOk E1 E2 128 84 b &&
      ((fastAnswer E1 E2 W2 128 84 b == (84 + b) % 97) == !(wrongRows.getD 84 []).contains b)) = true := by
  decide +kernel

/-- Row 84: the network answers (84 + b) % 97 exactly for the b outside row 84 of `wrongRows`. -/
theorem row_84 : ∀ b, b < 97 → (answer 84 b = (84 + b) % 97 ↔ b ∉ wrongRows.getD 84 []) := by
  intro b hb
  have h := fast_84 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 84 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 84 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_p97_H128_f0_30_wd0_3_s0.Trained

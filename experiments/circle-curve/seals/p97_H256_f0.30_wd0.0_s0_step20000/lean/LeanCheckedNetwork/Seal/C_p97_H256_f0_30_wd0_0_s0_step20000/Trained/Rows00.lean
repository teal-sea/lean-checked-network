import LeanCheckedNetwork.Seal.C_p97_H256_f0_30_wd0_0_s0_step20000.Trained.Table

/-! Rows 0 to 6 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_p97_H256_f0_30_wd0_0_s0_step20000.Trained

open LeanCheckedNetwork

theorem fast_0 : ∀ b, b < 97 →
    (fastOk E1 E2 256 0 b &&
      ((fastAnswer E1 E2 W2 256 0 b == (0 + b) % 97) == !(wrongRows.getD 0 []).contains b)) = true := by
  decide +kernel

/-- Row 0: the network answers (0 + b) % 97 exactly for the b outside row 0 of `wrongRows`. -/
theorem row_0 : ∀ b, b < 97 → (answer 0 b = (0 + b) % 97 ↔ b ∉ wrongRows.getD 0 []) := by
  intro b hb
  have h := fast_0 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 0 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 0 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_1 : ∀ b, b < 97 →
    (fastOk E1 E2 256 1 b &&
      ((fastAnswer E1 E2 W2 256 1 b == (1 + b) % 97) == !(wrongRows.getD 1 []).contains b)) = true := by
  decide +kernel

/-- Row 1: the network answers (1 + b) % 97 exactly for the b outside row 1 of `wrongRows`. -/
theorem row_1 : ∀ b, b < 97 → (answer 1 b = (1 + b) % 97 ↔ b ∉ wrongRows.getD 1 []) := by
  intro b hb
  have h := fast_1 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 1 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 1 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_2 : ∀ b, b < 97 →
    (fastOk E1 E2 256 2 b &&
      ((fastAnswer E1 E2 W2 256 2 b == (2 + b) % 97) == !(wrongRows.getD 2 []).contains b)) = true := by
  decide +kernel

/-- Row 2: the network answers (2 + b) % 97 exactly for the b outside row 2 of `wrongRows`. -/
theorem row_2 : ∀ b, b < 97 → (answer 2 b = (2 + b) % 97 ↔ b ∉ wrongRows.getD 2 []) := by
  intro b hb
  have h := fast_2 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 2 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 2 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_3 : ∀ b, b < 97 →
    (fastOk E1 E2 256 3 b &&
      ((fastAnswer E1 E2 W2 256 3 b == (3 + b) % 97) == !(wrongRows.getD 3 []).contains b)) = true := by
  decide +kernel

/-- Row 3: the network answers (3 + b) % 97 exactly for the b outside row 3 of `wrongRows`. -/
theorem row_3 : ∀ b, b < 97 → (answer 3 b = (3 + b) % 97 ↔ b ∉ wrongRows.getD 3 []) := by
  intro b hb
  have h := fast_3 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 3 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 3 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_4 : ∀ b, b < 97 →
    (fastOk E1 E2 256 4 b &&
      ((fastAnswer E1 E2 W2 256 4 b == (4 + b) % 97) == !(wrongRows.getD 4 []).contains b)) = true := by
  decide +kernel

/-- Row 4: the network answers (4 + b) % 97 exactly for the b outside row 4 of `wrongRows`. -/
theorem row_4 : ∀ b, b < 97 → (answer 4 b = (4 + b) % 97 ↔ b ∉ wrongRows.getD 4 []) := by
  intro b hb
  have h := fast_4 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 4 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 4 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_5 : ∀ b, b < 97 →
    (fastOk E1 E2 256 5 b &&
      ((fastAnswer E1 E2 W2 256 5 b == (5 + b) % 97) == !(wrongRows.getD 5 []).contains b)) = true := by
  decide +kernel

/-- Row 5: the network answers (5 + b) % 97 exactly for the b outside row 5 of `wrongRows`. -/
theorem row_5 : ∀ b, b < 97 → (answer 5 b = (5 + b) % 97 ↔ b ∉ wrongRows.getD 5 []) := by
  intro b hb
  have h := fast_5 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 5 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 5 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_6 : ∀ b, b < 97 →
    (fastOk E1 E2 256 6 b &&
      ((fastAnswer E1 E2 W2 256 6 b == (6 + b) % 97) == !(wrongRows.getD 6 []).contains b)) = true := by
  decide +kernel

/-- Row 6: the network answers (6 + b) % 97 exactly for the b outside row 6 of `wrongRows`. -/
theorem row_6 : ∀ b, b < 97 → (answer 6 b = (6 + b) % 97 ↔ b ∉ wrongRows.getD 6 []) := by
  intro b hb
  have h := fast_6 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 6 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 6 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_p97_H256_f0_30_wd0_0_s0_step20000.Trained

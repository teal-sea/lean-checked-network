import LeanCheckedNetwork.Seal.C_p97_H128_f0_30_wd0_3_s0.Trained.Table

/-! Rows 13 to 18 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_p97_H128_f0_30_wd0_3_s0.Trained

open LeanCheckedNetwork

theorem fast_13 : ∀ b, b < 97 →
    (fastOk E1 E2 128 13 b &&
      ((fastAnswer E1 E2 W2 128 13 b == (13 + b) % 97) == !(wrongRows.getD 13 []).contains b)) = true := by
  decide +kernel

/-- Row 13: the network answers (13 + b) % 97 exactly for the b outside row 13 of `wrongRows`. -/
theorem row_13 : ∀ b, b < 97 → (answer 13 b = (13 + b) % 97 ↔ b ∉ wrongRows.getD 13 []) := by
  intro b hb
  have h := fast_13 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 13 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 13 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_14 : ∀ b, b < 97 →
    (fastOk E1 E2 128 14 b &&
      ((fastAnswer E1 E2 W2 128 14 b == (14 + b) % 97) == !(wrongRows.getD 14 []).contains b)) = true := by
  decide +kernel

/-- Row 14: the network answers (14 + b) % 97 exactly for the b outside row 14 of `wrongRows`. -/
theorem row_14 : ∀ b, b < 97 → (answer 14 b = (14 + b) % 97 ↔ b ∉ wrongRows.getD 14 []) := by
  intro b hb
  have h := fast_14 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 14 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 14 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_15 : ∀ b, b < 97 →
    (fastOk E1 E2 128 15 b &&
      ((fastAnswer E1 E2 W2 128 15 b == (15 + b) % 97) == !(wrongRows.getD 15 []).contains b)) = true := by
  decide +kernel

/-- Row 15: the network answers (15 + b) % 97 exactly for the b outside row 15 of `wrongRows`. -/
theorem row_15 : ∀ b, b < 97 → (answer 15 b = (15 + b) % 97 ↔ b ∉ wrongRows.getD 15 []) := by
  intro b hb
  have h := fast_15 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 15 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 15 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_16 : ∀ b, b < 97 →
    (fastOk E1 E2 128 16 b &&
      ((fastAnswer E1 E2 W2 128 16 b == (16 + b) % 97) == !(wrongRows.getD 16 []).contains b)) = true := by
  decide +kernel

/-- Row 16: the network answers (16 + b) % 97 exactly for the b outside row 16 of `wrongRows`. -/
theorem row_16 : ∀ b, b < 97 → (answer 16 b = (16 + b) % 97 ↔ b ∉ wrongRows.getD 16 []) := by
  intro b hb
  have h := fast_16 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 16 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 16 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_17 : ∀ b, b < 97 →
    (fastOk E1 E2 128 17 b &&
      ((fastAnswer E1 E2 W2 128 17 b == (17 + b) % 97) == !(wrongRows.getD 17 []).contains b)) = true := by
  decide +kernel

/-- Row 17: the network answers (17 + b) % 97 exactly for the b outside row 17 of `wrongRows`. -/
theorem row_17 : ∀ b, b < 97 → (answer 17 b = (17 + b) % 97 ↔ b ∉ wrongRows.getD 17 []) := by
  intro b hb
  have h := fast_17 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 17 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 17 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_18 : ∀ b, b < 97 →
    (fastOk E1 E2 128 18 b &&
      ((fastAnswer E1 E2 W2 128 18 b == (18 + b) % 97) == !(wrongRows.getD 18 []).contains b)) = true := by
  decide +kernel

/-- Row 18: the network answers (18 + b) % 97 exactly for the b outside row 18 of `wrongRows`. -/
theorem row_18 : ∀ b, b < 97 → (answer 18 b = (18 + b) % 97 ↔ b ∉ wrongRows.getD 18 []) := by
  intro b hb
  have h := fast_18 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 18 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 18 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_p97_H128_f0_30_wd0_3_s0.Trained

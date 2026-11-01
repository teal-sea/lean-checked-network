import LeanCheckedNetwork.Seal.C_p97_H128_f0_50_wd0_1_s0.Trained.Table

/-! Rows 19 to 24 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_p97_H128_f0_50_wd0_1_s0.Trained

open LeanCheckedNetwork

theorem fast_19 : ∀ b, b < 97 →
    (fastOk E1 E2 128 19 b &&
      ((fastAnswer E1 E2 W2 128 19 b == (19 + b) % 97) == !(wrongRows.getD 19 []).contains b)) = true := by
  decide +kernel

/-- Row 19: the network answers (19 + b) % 97 exactly for the b outside row 19 of `wrongRows`. -/
theorem row_19 : ∀ b, b < 97 → (answer 19 b = (19 + b) % 97 ↔ b ∉ wrongRows.getD 19 []) := by
  intro b hb
  have h := fast_19 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 19 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 19 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_20 : ∀ b, b < 97 →
    (fastOk E1 E2 128 20 b &&
      ((fastAnswer E1 E2 W2 128 20 b == (20 + b) % 97) == !(wrongRows.getD 20 []).contains b)) = true := by
  decide +kernel

/-- Row 20: the network answers (20 + b) % 97 exactly for the b outside row 20 of `wrongRows`. -/
theorem row_20 : ∀ b, b < 97 → (answer 20 b = (20 + b) % 97 ↔ b ∉ wrongRows.getD 20 []) := by
  intro b hb
  have h := fast_20 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 20 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 20 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_21 : ∀ b, b < 97 →
    (fastOk E1 E2 128 21 b &&
      ((fastAnswer E1 E2 W2 128 21 b == (21 + b) % 97) == !(wrongRows.getD 21 []).contains b)) = true := by
  decide +kernel

/-- Row 21: the network answers (21 + b) % 97 exactly for the b outside row 21 of `wrongRows`. -/
theorem row_21 : ∀ b, b < 97 → (answer 21 b = (21 + b) % 97 ↔ b ∉ wrongRows.getD 21 []) := by
  intro b hb
  have h := fast_21 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 21 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 21 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_22 : ∀ b, b < 97 →
    (fastOk E1 E2 128 22 b &&
      ((fastAnswer E1 E2 W2 128 22 b == (22 + b) % 97) == !(wrongRows.getD 22 []).contains b)) = true := by
  decide +kernel

/-- Row 22: the network answers (22 + b) % 97 exactly for the b outside row 22 of `wrongRows`. -/
theorem row_22 : ∀ b, b < 97 → (answer 22 b = (22 + b) % 97 ↔ b ∉ wrongRows.getD 22 []) := by
  intro b hb
  have h := fast_22 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 22 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 22 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_23 : ∀ b, b < 97 →
    (fastOk E1 E2 128 23 b &&
      ((fastAnswer E1 E2 W2 128 23 b == (23 + b) % 97) == !(wrongRows.getD 23 []).contains b)) = true := by
  decide +kernel

/-- Row 23: the network answers (23 + b) % 97 exactly for the b outside row 23 of `wrongRows`. -/
theorem row_23 : ∀ b, b < 97 → (answer 23 b = (23 + b) % 97 ↔ b ∉ wrongRows.getD 23 []) := by
  intro b hb
  have h := fast_23 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 23 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 23 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_24 : ∀ b, b < 97 →
    (fastOk E1 E2 128 24 b &&
      ((fastAnswer E1 E2 W2 128 24 b == (24 + b) % 97) == !(wrongRows.getD 24 []).contains b)) = true := by
  decide +kernel

/-- Row 24: the network answers (24 + b) % 97 exactly for the b outside row 24 of `wrongRows`. -/
theorem row_24 : ∀ b, b < 97 → (answer 24 b = (24 + b) % 97 ↔ b ∉ wrongRows.getD 24 []) := by
  intro b hb
  have h := fast_24 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 24 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 24 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_p97_H128_f0_50_wd0_1_s0.Trained

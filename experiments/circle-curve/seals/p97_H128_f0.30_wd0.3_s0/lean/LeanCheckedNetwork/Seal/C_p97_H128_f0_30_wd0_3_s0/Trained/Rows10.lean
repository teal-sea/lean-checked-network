import LeanCheckedNetwork.Seal.C_p97_H128_f0_30_wd0_3_s0.Trained.Table

/-! Rows 61 to 66 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_p97_H128_f0_30_wd0_3_s0.Trained

open LeanCheckedNetwork

theorem fast_61 : ∀ b, b < 97 →
    (fastOk E1 E2 128 61 b &&
      ((fastAnswer E1 E2 W2 128 61 b == (61 + b) % 97) == !(wrongRows.getD 61 []).contains b)) = true := by
  decide +kernel

/-- Row 61: the network answers (61 + b) % 97 exactly for the b outside row 61 of `wrongRows`. -/
theorem row_61 : ∀ b, b < 97 → (answer 61 b = (61 + b) % 97 ↔ b ∉ wrongRows.getD 61 []) := by
  intro b hb
  have h := fast_61 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 61 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 61 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_62 : ∀ b, b < 97 →
    (fastOk E1 E2 128 62 b &&
      ((fastAnswer E1 E2 W2 128 62 b == (62 + b) % 97) == !(wrongRows.getD 62 []).contains b)) = true := by
  decide +kernel

/-- Row 62: the network answers (62 + b) % 97 exactly for the b outside row 62 of `wrongRows`. -/
theorem row_62 : ∀ b, b < 97 → (answer 62 b = (62 + b) % 97 ↔ b ∉ wrongRows.getD 62 []) := by
  intro b hb
  have h := fast_62 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 62 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 62 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_63 : ∀ b, b < 97 →
    (fastOk E1 E2 128 63 b &&
      ((fastAnswer E1 E2 W2 128 63 b == (63 + b) % 97) == !(wrongRows.getD 63 []).contains b)) = true := by
  decide +kernel

/-- Row 63: the network answers (63 + b) % 97 exactly for the b outside row 63 of `wrongRows`. -/
theorem row_63 : ∀ b, b < 97 → (answer 63 b = (63 + b) % 97 ↔ b ∉ wrongRows.getD 63 []) := by
  intro b hb
  have h := fast_63 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 63 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 63 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_64 : ∀ b, b < 97 →
    (fastOk E1 E2 128 64 b &&
      ((fastAnswer E1 E2 W2 128 64 b == (64 + b) % 97) == !(wrongRows.getD 64 []).contains b)) = true := by
  decide +kernel

/-- Row 64: the network answers (64 + b) % 97 exactly for the b outside row 64 of `wrongRows`. -/
theorem row_64 : ∀ b, b < 97 → (answer 64 b = (64 + b) % 97 ↔ b ∉ wrongRows.getD 64 []) := by
  intro b hb
  have h := fast_64 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 64 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 64 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_65 : ∀ b, b < 97 →
    (fastOk E1 E2 128 65 b &&
      ((fastAnswer E1 E2 W2 128 65 b == (65 + b) % 97) == !(wrongRows.getD 65 []).contains b)) = true := by
  decide +kernel

/-- Row 65: the network answers (65 + b) % 97 exactly for the b outside row 65 of `wrongRows`. -/
theorem row_65 : ∀ b, b < 97 → (answer 65 b = (65 + b) % 97 ↔ b ∉ wrongRows.getD 65 []) := by
  intro b hb
  have h := fast_65 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 65 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 65 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_66 : ∀ b, b < 97 →
    (fastOk E1 E2 128 66 b &&
      ((fastAnswer E1 E2 W2 128 66 b == (66 + b) % 97) == !(wrongRows.getD 66 []).contains b)) = true := by
  decide +kernel

/-- Row 66: the network answers (66 + b) % 97 exactly for the b outside row 66 of `wrongRows`. -/
theorem row_66 : ∀ b, b < 97 → (answer 66 b = (66 + b) % 97 ↔ b ∉ wrongRows.getD 66 []) := by
  intro b hb
  have h := fast_66 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 66 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 66 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_p97_H128_f0_30_wd0_3_s0.Trained

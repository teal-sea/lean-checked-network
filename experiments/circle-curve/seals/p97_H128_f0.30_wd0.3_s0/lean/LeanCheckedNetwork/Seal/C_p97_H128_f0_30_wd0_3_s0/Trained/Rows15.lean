import LeanCheckedNetwork.Seal.C_p97_H128_f0_30_wd0_3_s0.Trained.Table

/-! Rows 91 to 96 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_p97_H128_f0_30_wd0_3_s0.Trained

open LeanCheckedNetwork

theorem fast_91 : ∀ b, b < 97 →
    (fastOk E1 E2 128 91 b &&
      ((fastAnswer E1 E2 W2 128 91 b == (91 + b) % 97) == !(wrongRows.getD 91 []).contains b)) = true := by
  decide +kernel

/-- Row 91: the network answers (91 + b) % 97 exactly for the b outside row 91 of `wrongRows`. -/
theorem row_91 : ∀ b, b < 97 → (answer 91 b = (91 + b) % 97 ↔ b ∉ wrongRows.getD 91 []) := by
  intro b hb
  have h := fast_91 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 91 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 91 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_92 : ∀ b, b < 97 →
    (fastOk E1 E2 128 92 b &&
      ((fastAnswer E1 E2 W2 128 92 b == (92 + b) % 97) == !(wrongRows.getD 92 []).contains b)) = true := by
  decide +kernel

/-- Row 92: the network answers (92 + b) % 97 exactly for the b outside row 92 of `wrongRows`. -/
theorem row_92 : ∀ b, b < 97 → (answer 92 b = (92 + b) % 97 ↔ b ∉ wrongRows.getD 92 []) := by
  intro b hb
  have h := fast_92 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 92 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 92 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_93 : ∀ b, b < 97 →
    (fastOk E1 E2 128 93 b &&
      ((fastAnswer E1 E2 W2 128 93 b == (93 + b) % 97) == !(wrongRows.getD 93 []).contains b)) = true := by
  decide +kernel

/-- Row 93: the network answers (93 + b) % 97 exactly for the b outside row 93 of `wrongRows`. -/
theorem row_93 : ∀ b, b < 97 → (answer 93 b = (93 + b) % 97 ↔ b ∉ wrongRows.getD 93 []) := by
  intro b hb
  have h := fast_93 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 93 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 93 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_94 : ∀ b, b < 97 →
    (fastOk E1 E2 128 94 b &&
      ((fastAnswer E1 E2 W2 128 94 b == (94 + b) % 97) == !(wrongRows.getD 94 []).contains b)) = true := by
  decide +kernel

/-- Row 94: the network answers (94 + b) % 97 exactly for the b outside row 94 of `wrongRows`. -/
theorem row_94 : ∀ b, b < 97 → (answer 94 b = (94 + b) % 97 ↔ b ∉ wrongRows.getD 94 []) := by
  intro b hb
  have h := fast_94 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 94 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 94 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_95 : ∀ b, b < 97 →
    (fastOk E1 E2 128 95 b &&
      ((fastAnswer E1 E2 W2 128 95 b == (95 + b) % 97) == !(wrongRows.getD 95 []).contains b)) = true := by
  decide +kernel

/-- Row 95: the network answers (95 + b) % 97 exactly for the b outside row 95 of `wrongRows`. -/
theorem row_95 : ∀ b, b < 97 → (answer 95 b = (95 + b) % 97 ↔ b ∉ wrongRows.getD 95 []) := by
  intro b hb
  have h := fast_95 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 95 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 95 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_96 : ∀ b, b < 97 →
    (fastOk E1 E2 128 96 b &&
      ((fastAnswer E1 E2 W2 128 96 b == (96 + b) % 97) == !(wrongRows.getD 96 []).contains b)) = true := by
  decide +kernel

/-- Row 96: the network answers (96 + b) % 97 exactly for the b outside row 96 of `wrongRows`. -/
theorem row_96 : ∀ b, b < 97 → (answer 96 b = (96 + b) % 97 ↔ b ∉ wrongRows.getD 96 []) := by
  intro b hb
  have h := fast_96 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 96 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 96 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_p97_H128_f0_30_wd0_3_s0.Trained

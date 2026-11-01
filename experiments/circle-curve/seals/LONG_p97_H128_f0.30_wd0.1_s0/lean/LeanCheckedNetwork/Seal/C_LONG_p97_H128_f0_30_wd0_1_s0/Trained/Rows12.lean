import LeanCheckedNetwork.Seal.C_LONG_p97_H128_f0_30_wd0_1_s0.Trained.Table

/-! Rows 73 to 78 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_LONG_p97_H128_f0_30_wd0_1_s0.Trained

open LeanCheckedNetwork

theorem fast_73 : ∀ b, b < 97 →
    (fastOk E1 E2 128 73 b &&
      ((fastAnswer E1 E2 W2 128 73 b == (73 + b) % 97) == !(wrongRows.getD 73 []).contains b)) = true := by
  decide +kernel

/-- Row 73: the network answers (73 + b) % 97 exactly for the b outside row 73 of `wrongRows`. -/
theorem row_73 : ∀ b, b < 97 → (answer 73 b = (73 + b) % 97 ↔ b ∉ wrongRows.getD 73 []) := by
  intro b hb
  have h := fast_73 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 73 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 73 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_74 : ∀ b, b < 97 →
    (fastOk E1 E2 128 74 b &&
      ((fastAnswer E1 E2 W2 128 74 b == (74 + b) % 97) == !(wrongRows.getD 74 []).contains b)) = true := by
  decide +kernel

/-- Row 74: the network answers (74 + b) % 97 exactly for the b outside row 74 of `wrongRows`. -/
theorem row_74 : ∀ b, b < 97 → (answer 74 b = (74 + b) % 97 ↔ b ∉ wrongRows.getD 74 []) := by
  intro b hb
  have h := fast_74 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 74 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 74 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_75 : ∀ b, b < 97 →
    (fastOk E1 E2 128 75 b &&
      ((fastAnswer E1 E2 W2 128 75 b == (75 + b) % 97) == !(wrongRows.getD 75 []).contains b)) = true := by
  decide +kernel

/-- Row 75: the network answers (75 + b) % 97 exactly for the b outside row 75 of `wrongRows`. -/
theorem row_75 : ∀ b, b < 97 → (answer 75 b = (75 + b) % 97 ↔ b ∉ wrongRows.getD 75 []) := by
  intro b hb
  have h := fast_75 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 75 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 75 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_76 : ∀ b, b < 97 →
    (fastOk E1 E2 128 76 b &&
      ((fastAnswer E1 E2 W2 128 76 b == (76 + b) % 97) == !(wrongRows.getD 76 []).contains b)) = true := by
  decide +kernel

/-- Row 76: the network answers (76 + b) % 97 exactly for the b outside row 76 of `wrongRows`. -/
theorem row_76 : ∀ b, b < 97 → (answer 76 b = (76 + b) % 97 ↔ b ∉ wrongRows.getD 76 []) := by
  intro b hb
  have h := fast_76 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 76 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 76 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_77 : ∀ b, b < 97 →
    (fastOk E1 E2 128 77 b &&
      ((fastAnswer E1 E2 W2 128 77 b == (77 + b) % 97) == !(wrongRows.getD 77 []).contains b)) = true := by
  decide +kernel

/-- Row 77: the network answers (77 + b) % 97 exactly for the b outside row 77 of `wrongRows`. -/
theorem row_77 : ∀ b, b < 97 → (answer 77 b = (77 + b) % 97 ↔ b ∉ wrongRows.getD 77 []) := by
  intro b hb
  have h := fast_77 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 77 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 77 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_78 : ∀ b, b < 97 →
    (fastOk E1 E2 128 78 b &&
      ((fastAnswer E1 E2 W2 128 78 b == (78 + b) % 97) == !(wrongRows.getD 78 []).contains b)) = true := by
  decide +kernel

/-- Row 78: the network answers (78 + b) % 97 exactly for the b outside row 78 of `wrongRows`. -/
theorem row_78 : ∀ b, b < 97 → (answer 78 b = (78 + b) % 97 ↔ b ∉ wrongRows.getD 78 []) := by
  intro b hb
  have h := fast_78 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 78 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 128 78 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_LONG_p97_H128_f0_30_wd0_1_s0.Trained

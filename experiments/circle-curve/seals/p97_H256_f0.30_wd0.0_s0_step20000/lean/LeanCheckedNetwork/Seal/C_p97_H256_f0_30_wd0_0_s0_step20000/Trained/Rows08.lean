import LeanCheckedNetwork.Seal.C_p97_H256_f0_30_wd0_0_s0_step20000.Trained.Table

/-! Rows 49 to 54 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_p97_H256_f0_30_wd0_0_s0_step20000.Trained

open LeanCheckedNetwork

theorem fast_49 : ∀ b, b < 97 →
    (fastOk E1 E2 256 49 b &&
      ((fastAnswer E1 E2 W2 256 49 b == (49 + b) % 97) == !(wrongRows.getD 49 []).contains b)) = true := by
  decide +kernel

/-- Row 49: the network answers (49 + b) % 97 exactly for the b outside row 49 of `wrongRows`. -/
theorem row_49 : ∀ b, b < 97 → (answer 49 b = (49 + b) % 97 ↔ b ∉ wrongRows.getD 49 []) := by
  intro b hb
  have h := fast_49 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 49 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 49 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_50 : ∀ b, b < 97 →
    (fastOk E1 E2 256 50 b &&
      ((fastAnswer E1 E2 W2 256 50 b == (50 + b) % 97) == !(wrongRows.getD 50 []).contains b)) = true := by
  decide +kernel

/-- Row 50: the network answers (50 + b) % 97 exactly for the b outside row 50 of `wrongRows`. -/
theorem row_50 : ∀ b, b < 97 → (answer 50 b = (50 + b) % 97 ↔ b ∉ wrongRows.getD 50 []) := by
  intro b hb
  have h := fast_50 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 50 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 50 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_51 : ∀ b, b < 97 →
    (fastOk E1 E2 256 51 b &&
      ((fastAnswer E1 E2 W2 256 51 b == (51 + b) % 97) == !(wrongRows.getD 51 []).contains b)) = true := by
  decide +kernel

/-- Row 51: the network answers (51 + b) % 97 exactly for the b outside row 51 of `wrongRows`. -/
theorem row_51 : ∀ b, b < 97 → (answer 51 b = (51 + b) % 97 ↔ b ∉ wrongRows.getD 51 []) := by
  intro b hb
  have h := fast_51 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 51 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 51 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_52 : ∀ b, b < 97 →
    (fastOk E1 E2 256 52 b &&
      ((fastAnswer E1 E2 W2 256 52 b == (52 + b) % 97) == !(wrongRows.getD 52 []).contains b)) = true := by
  decide +kernel

/-- Row 52: the network answers (52 + b) % 97 exactly for the b outside row 52 of `wrongRows`. -/
theorem row_52 : ∀ b, b < 97 → (answer 52 b = (52 + b) % 97 ↔ b ∉ wrongRows.getD 52 []) := by
  intro b hb
  have h := fast_52 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 52 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 52 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_53 : ∀ b, b < 97 →
    (fastOk E1 E2 256 53 b &&
      ((fastAnswer E1 E2 W2 256 53 b == (53 + b) % 97) == !(wrongRows.getD 53 []).contains b)) = true := by
  decide +kernel

/-- Row 53: the network answers (53 + b) % 97 exactly for the b outside row 53 of `wrongRows`. -/
theorem row_53 : ∀ b, b < 97 → (answer 53 b = (53 + b) % 97 ↔ b ∉ wrongRows.getD 53 []) := by
  intro b hb
  have h := fast_53 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 53 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 53 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_54 : ∀ b, b < 97 →
    (fastOk E1 E2 256 54 b &&
      ((fastAnswer E1 E2 W2 256 54 b == (54 + b) % 97) == !(wrongRows.getD 54 []).contains b)) = true := by
  decide +kernel

/-- Row 54: the network answers (54 + b) % 97 exactly for the b outside row 54 of `wrongRows`. -/
theorem row_54 : ∀ b, b < 97 → (answer 54 b = (54 + b) % 97 ↔ b ∉ wrongRows.getD 54 []) := by
  intro b hb
  have h := fast_54 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 54 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 54 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_p97_H256_f0_30_wd0_0_s0_step20000.Trained

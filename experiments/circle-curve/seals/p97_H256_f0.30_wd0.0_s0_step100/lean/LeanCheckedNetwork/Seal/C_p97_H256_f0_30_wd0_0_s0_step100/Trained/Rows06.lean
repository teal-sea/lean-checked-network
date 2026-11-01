import LeanCheckedNetwork.Seal.C_p97_H256_f0_30_wd0_0_s0_step100.Trained.Table

/-! Rows 37 to 42 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_p97_H256_f0_30_wd0_0_s0_step100.Trained

open LeanCheckedNetwork

theorem fast_37 : ∀ b, b < 97 →
    (fastOk E1 E2 256 37 b &&
      ((fastAnswer E1 E2 W2 256 37 b == (37 + b) % 97) == !(wrongRows.getD 37 []).contains b)) = true := by
  decide +kernel

/-- Row 37: the network answers (37 + b) % 97 exactly for the b outside row 37 of `wrongRows`. -/
theorem row_37 : ∀ b, b < 97 → (answer 37 b = (37 + b) % 97 ↔ b ∉ wrongRows.getD 37 []) := by
  intro b hb
  have h := fast_37 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 37 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 37 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_38 : ∀ b, b < 97 →
    (fastOk E1 E2 256 38 b &&
      ((fastAnswer E1 E2 W2 256 38 b == (38 + b) % 97) == !(wrongRows.getD 38 []).contains b)) = true := by
  decide +kernel

/-- Row 38: the network answers (38 + b) % 97 exactly for the b outside row 38 of `wrongRows`. -/
theorem row_38 : ∀ b, b < 97 → (answer 38 b = (38 + b) % 97 ↔ b ∉ wrongRows.getD 38 []) := by
  intro b hb
  have h := fast_38 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 38 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 38 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_39 : ∀ b, b < 97 →
    (fastOk E1 E2 256 39 b &&
      ((fastAnswer E1 E2 W2 256 39 b == (39 + b) % 97) == !(wrongRows.getD 39 []).contains b)) = true := by
  decide +kernel

/-- Row 39: the network answers (39 + b) % 97 exactly for the b outside row 39 of `wrongRows`. -/
theorem row_39 : ∀ b, b < 97 → (answer 39 b = (39 + b) % 97 ↔ b ∉ wrongRows.getD 39 []) := by
  intro b hb
  have h := fast_39 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 39 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 39 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_40 : ∀ b, b < 97 →
    (fastOk E1 E2 256 40 b &&
      ((fastAnswer E1 E2 W2 256 40 b == (40 + b) % 97) == !(wrongRows.getD 40 []).contains b)) = true := by
  decide +kernel

/-- Row 40: the network answers (40 + b) % 97 exactly for the b outside row 40 of `wrongRows`. -/
theorem row_40 : ∀ b, b < 97 → (answer 40 b = (40 + b) % 97 ↔ b ∉ wrongRows.getD 40 []) := by
  intro b hb
  have h := fast_40 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 40 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 40 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_41 : ∀ b, b < 97 →
    (fastOk E1 E2 256 41 b &&
      ((fastAnswer E1 E2 W2 256 41 b == (41 + b) % 97) == !(wrongRows.getD 41 []).contains b)) = true := by
  decide +kernel

/-- Row 41: the network answers (41 + b) % 97 exactly for the b outside row 41 of `wrongRows`. -/
theorem row_41 : ∀ b, b < 97 → (answer 41 b = (41 + b) % 97 ↔ b ∉ wrongRows.getD 41 []) := by
  intro b hb
  have h := fast_41 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 41 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 41 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_42 : ∀ b, b < 97 →
    (fastOk E1 E2 256 42 b &&
      ((fastAnswer E1 E2 W2 256 42 b == (42 + b) % 97) == !(wrongRows.getD 42 []).contains b)) = true := by
  decide +kernel

/-- Row 42: the network answers (42 + b) % 97 exactly for the b outside row 42 of `wrongRows`. -/
theorem row_42 : ∀ b, b < 97 → (answer 42 b = (42 + b) % 97 ↔ b ∉ wrongRows.getD 42 []) := by
  intro b hb
  have h := fast_42 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 42 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 256 42 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_p97_H256_f0_30_wd0_0_s0_step100.Trained

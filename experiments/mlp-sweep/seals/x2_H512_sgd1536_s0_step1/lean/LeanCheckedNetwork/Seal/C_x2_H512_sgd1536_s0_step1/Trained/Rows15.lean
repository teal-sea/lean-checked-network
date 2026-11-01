import LeanCheckedNetwork.Seal.C_x2_H512_sgd1536_s0_step1.Trained.Table

/-! Rows 46 to 48 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H512_sgd1536_s0_step1.Trained

open LeanCheckedNetwork

theorem fast_46 : ∀ b, b < 97 →
    (fastOk E1 E2 512 46 b &&
      ((fastAnswer E1 E2 W2 512 46 b == (46 + b) % 97) == !(wrongRows.getD 46 []).contains b)) = true := by
  decide +kernel

/-- Row 46: the network answers (46 + b) % 97 exactly for the b outside row 46 of `wrongRows`. -/
theorem row_46 : ∀ b, b < 97 → (answer 46 b = (46 + b) % 97 ↔ b ∉ wrongRows.getD 46 []) := by
  intro b hb
  have h := fast_46 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 46 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 46 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_47 : ∀ b, b < 97 →
    (fastOk E1 E2 512 47 b &&
      ((fastAnswer E1 E2 W2 512 47 b == (47 + b) % 97) == !(wrongRows.getD 47 []).contains b)) = true := by
  decide +kernel

/-- Row 47: the network answers (47 + b) % 97 exactly for the b outside row 47 of `wrongRows`. -/
theorem row_47 : ∀ b, b < 97 → (answer 47 b = (47 + b) % 97 ↔ b ∉ wrongRows.getD 47 []) := by
  intro b hb
  have h := fast_47 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 47 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 47 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_48 : ∀ b, b < 97 →
    (fastOk E1 E2 512 48 b &&
      ((fastAnswer E1 E2 W2 512 48 b == (48 + b) % 97) == !(wrongRows.getD 48 []).contains b)) = true := by
  decide +kernel

/-- Row 48: the network answers (48 + b) % 97 exactly for the b outside row 48 of `wrongRows`. -/
theorem row_48 : ∀ b, b < 97 → (answer 48 b = (48 + b) % 97 ↔ b ∉ wrongRows.getD 48 []) := by
  intro b hb
  have h := fast_48 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 48 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 48 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H512_sgd1536_s0_step1.Trained

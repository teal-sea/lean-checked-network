import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s0_step1.Trained.Table

/-! Rows 58 to 60 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H512_lr002_s0_step1.Trained

open LeanCheckedNetwork

theorem fast_58 : ∀ b, b < 97 →
    (fastOk E1 E2 512 58 b &&
      ((fastAnswer E1 E2 W2 512 58 b == (58 + b) % 97) == !(wrongRows.getD 58 []).contains b)) = true := by
  decide +kernel

/-- Row 58: the network answers (58 + b) % 97 exactly for the b outside row 58 of `wrongRows`. -/
theorem row_58 : ∀ b, b < 97 → (answer 58 b = (58 + b) % 97 ↔ b ∉ wrongRows.getD 58 []) := by
  intro b hb
  have h := fast_58 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 58 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 58 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_59 : ∀ b, b < 97 →
    (fastOk E1 E2 512 59 b &&
      ((fastAnswer E1 E2 W2 512 59 b == (59 + b) % 97) == !(wrongRows.getD 59 []).contains b)) = true := by
  decide +kernel

/-- Row 59: the network answers (59 + b) % 97 exactly for the b outside row 59 of `wrongRows`. -/
theorem row_59 : ∀ b, b < 97 → (answer 59 b = (59 + b) % 97 ↔ b ∉ wrongRows.getD 59 []) := by
  intro b hb
  have h := fast_59 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 59 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 59 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_60 : ∀ b, b < 97 →
    (fastOk E1 E2 512 60 b &&
      ((fastAnswer E1 E2 W2 512 60 b == (60 + b) % 97) == !(wrongRows.getD 60 []).contains b)) = true := by
  decide +kernel

/-- Row 60: the network answers (60 + b) % 97 exactly for the b outside row 60 of `wrongRows`. -/
theorem row_60 : ∀ b, b < 97 → (answer 60 b = (60 + b) % 97 ↔ b ∉ wrongRows.getD 60 []) := by
  intro b hb
  have h := fast_60 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 60 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 60 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H512_lr002_s0_step1.Trained

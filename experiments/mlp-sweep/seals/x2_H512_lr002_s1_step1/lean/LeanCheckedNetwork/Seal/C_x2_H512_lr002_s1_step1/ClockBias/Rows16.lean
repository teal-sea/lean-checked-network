import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias.Table

/-! Rows 49 to 51 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias

open LeanCheckedNetwork

theorem fast_49 : ∀ b, b < 97 →
    (fastOk E1 E2 512 49 b &&
      ((fastAnswer E1 E2 W2 512 49 b == (49 + b) % 97) == !(wrongRows.getD 49 []).contains b)) = true := by
  decide +kernel

/-- Row 49: the network answers (49 + b) % 97 exactly for the b outside row 49 of `wrongRows`. -/
theorem row_49 : ∀ b, b < 97 → (answer 49 b = (49 + b) % 97 ↔ b ∉ wrongRows.getD 49 []) := by
  intro b hb
  have h := fast_49 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 49 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 49 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_50 : ∀ b, b < 97 →
    (fastOk E1 E2 512 50 b &&
      ((fastAnswer E1 E2 W2 512 50 b == (50 + b) % 97) == !(wrongRows.getD 50 []).contains b)) = true := by
  decide +kernel

/-- Row 50: the network answers (50 + b) % 97 exactly for the b outside row 50 of `wrongRows`. -/
theorem row_50 : ∀ b, b < 97 → (answer 50 b = (50 + b) % 97 ↔ b ∉ wrongRows.getD 50 []) := by
  intro b hb
  have h := fast_50 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 50 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 50 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_51 : ∀ b, b < 97 →
    (fastOk E1 E2 512 51 b &&
      ((fastAnswer E1 E2 W2 512 51 b == (51 + b) % 97) == !(wrongRows.getD 51 []).contains b)) = true := by
  decide +kernel

/-- Row 51: the network answers (51 + b) % 97 exactly for the b outside row 51 of `wrongRows`. -/
theorem row_51 : ∀ b, b < 97 → (answer 51 b = (51 + b) % 97 ↔ b ∉ wrongRows.getD 51 []) := by
  intro b hb
  have h := fast_51 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 51 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 51 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H512_lr002_s1_step1.ClockBias

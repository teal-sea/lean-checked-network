import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s2_step1.ClockBias.Table

/-! Rows 4 to 6 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H512_lr002_s2_step1.ClockBias

open LeanCheckedNetwork

theorem fast_4 : ∀ b, b < 97 →
    (fastOk E1 E2 512 4 b &&
      ((fastAnswer E1 E2 W2 512 4 b == (4 + b) % 97) == !(wrongRows.getD 4 []).contains b)) = true := by
  decide +kernel

/-- Row 4: the network answers (4 + b) % 97 exactly for the b outside row 4 of `wrongRows`. -/
theorem row_4 : ∀ b, b < 97 → (answer 4 b = (4 + b) % 97 ↔ b ∉ wrongRows.getD 4 []) := by
  intro b hb
  have h := fast_4 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 4 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 4 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_5 : ∀ b, b < 97 →
    (fastOk E1 E2 512 5 b &&
      ((fastAnswer E1 E2 W2 512 5 b == (5 + b) % 97) == !(wrongRows.getD 5 []).contains b)) = true := by
  decide +kernel

/-- Row 5: the network answers (5 + b) % 97 exactly for the b outside row 5 of `wrongRows`. -/
theorem row_5 : ∀ b, b < 97 → (answer 5 b = (5 + b) % 97 ↔ b ∉ wrongRows.getD 5 []) := by
  intro b hb
  have h := fast_5 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 5 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 5 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_6 : ∀ b, b < 97 →
    (fastOk E1 E2 512 6 b &&
      ((fastAnswer E1 E2 W2 512 6 b == (6 + b) % 97) == !(wrongRows.getD 6 []).contains b)) = true := by
  decide +kernel

/-- Row 6: the network answers (6 + b) % 97 exactly for the b outside row 6 of `wrongRows`. -/
theorem row_6 : ∀ b, b < 97 → (answer 6 b = (6 + b) % 97 ↔ b ∉ wrongRows.getD 6 []) := by
  intro b hb
  have h := fast_6 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 6 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 6 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H512_lr002_s2_step1.ClockBias

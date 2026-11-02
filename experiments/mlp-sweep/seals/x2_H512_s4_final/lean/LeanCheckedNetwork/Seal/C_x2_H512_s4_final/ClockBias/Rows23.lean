import LeanCheckedNetwork.Seal.C_x2_H512_s4_final.ClockBias.Table

/-! Rows 70 to 72 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H512_s4_final.ClockBias

open LeanCheckedNetwork

theorem fast_70 : ∀ b, b < 97 →
    (fastOk E1 E2 512 70 b &&
      ((fastAnswer E1 E2 W2 512 70 b == (70 + b) % 97) == !(wrongRows.getD 70 []).contains b)) = true := by
  decide +kernel

/-- Row 70: the network answers (70 + b) % 97 exactly for the b outside row 70 of `wrongRows`. -/
theorem row_70 : ∀ b, b < 97 → (answer 70 b = (70 + b) % 97 ↔ b ∉ wrongRows.getD 70 []) := by
  intro b hb
  have h := fast_70 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 70 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 70 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_71 : ∀ b, b < 97 →
    (fastOk E1 E2 512 71 b &&
      ((fastAnswer E1 E2 W2 512 71 b == (71 + b) % 97) == !(wrongRows.getD 71 []).contains b)) = true := by
  decide +kernel

/-- Row 71: the network answers (71 + b) % 97 exactly for the b outside row 71 of `wrongRows`. -/
theorem row_71 : ∀ b, b < 97 → (answer 71 b = (71 + b) % 97 ↔ b ∉ wrongRows.getD 71 []) := by
  intro b hb
  have h := fast_71 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 71 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 71 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_72 : ∀ b, b < 97 →
    (fastOk E1 E2 512 72 b &&
      ((fastAnswer E1 E2 W2 512 72 b == (72 + b) % 97) == !(wrongRows.getD 72 []).contains b)) = true := by
  decide +kernel

/-- Row 72: the network answers (72 + b) % 97 exactly for the b outside row 72 of `wrongRows`. -/
theorem row_72 : ∀ b, b < 97 → (answer 72 b = (72 + b) % 97 ↔ b ∉ wrongRows.getD 72 []) := by
  intro b hb
  have h := fast_72 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 72 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 72 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H512_s4_final.ClockBias

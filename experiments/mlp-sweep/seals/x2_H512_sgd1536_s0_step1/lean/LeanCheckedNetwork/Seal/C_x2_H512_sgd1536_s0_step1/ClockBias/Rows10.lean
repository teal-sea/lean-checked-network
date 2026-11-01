import LeanCheckedNetwork.Seal.C_x2_H512_sgd1536_s0_step1.ClockBias.Table

/-! Rows 31 to 33 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H512_sgd1536_s0_step1.ClockBias

open LeanCheckedNetwork

theorem fast_31 : ∀ b, b < 97 →
    (fastOk E1 E2 512 31 b &&
      ((fastAnswer E1 E2 W2 512 31 b == (31 + b) % 97) == !(wrongRows.getD 31 []).contains b)) = true := by
  decide +kernel

/-- Row 31: the network answers (31 + b) % 97 exactly for the b outside row 31 of `wrongRows`. -/
theorem row_31 : ∀ b, b < 97 → (answer 31 b = (31 + b) % 97 ↔ b ∉ wrongRows.getD 31 []) := by
  intro b hb
  have h := fast_31 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 31 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 31 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_32 : ∀ b, b < 97 →
    (fastOk E1 E2 512 32 b &&
      ((fastAnswer E1 E2 W2 512 32 b == (32 + b) % 97) == !(wrongRows.getD 32 []).contains b)) = true := by
  decide +kernel

/-- Row 32: the network answers (32 + b) % 97 exactly for the b outside row 32 of `wrongRows`. -/
theorem row_32 : ∀ b, b < 97 → (answer 32 b = (32 + b) % 97 ↔ b ∉ wrongRows.getD 32 []) := by
  intro b hb
  have h := fast_32 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 32 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 32 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_33 : ∀ b, b < 97 →
    (fastOk E1 E2 512 33 b &&
      ((fastAnswer E1 E2 W2 512 33 b == (33 + b) % 97) == !(wrongRows.getD 33 []).contains b)) = true := by
  decide +kernel

/-- Row 33: the network answers (33 + b) % 97 exactly for the b outside row 33 of `wrongRows`. -/
theorem row_33 : ∀ b, b < 97 → (answer 33 b = (33 + b) % 97 ↔ b ∉ wrongRows.getD 33 []) := by
  intro b hb
  have h := fast_33 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 33 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 33 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H512_sgd1536_s0_step1.ClockBias

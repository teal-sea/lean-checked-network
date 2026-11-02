import LeanCheckedNetwork.Seal.C_x2_H512_lr002_s0_step1.ClockBias.Table

/-! Rows 85 to 87 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H512_lr002_s0_step1.ClockBias

open LeanCheckedNetwork

theorem fast_85 : ∀ b, b < 97 →
    (fastOk E1 E2 512 85 b &&
      ((fastAnswer E1 E2 W2 512 85 b == (85 + b) % 97) == !(wrongRows.getD 85 []).contains b)) = true := by
  decide +kernel

/-- Row 85: the network answers (85 + b) % 97 exactly for the b outside row 85 of `wrongRows`. -/
theorem row_85 : ∀ b, b < 97 → (answer 85 b = (85 + b) % 97 ↔ b ∉ wrongRows.getD 85 []) := by
  intro b hb
  have h := fast_85 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 85 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 85 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_86 : ∀ b, b < 97 →
    (fastOk E1 E2 512 86 b &&
      ((fastAnswer E1 E2 W2 512 86 b == (86 + b) % 97) == !(wrongRows.getD 86 []).contains b)) = true := by
  decide +kernel

/-- Row 86: the network answers (86 + b) % 97 exactly for the b outside row 86 of `wrongRows`. -/
theorem row_86 : ∀ b, b < 97 → (answer 86 b = (86 + b) % 97 ↔ b ∉ wrongRows.getD 86 []) := by
  intro b hb
  have h := fast_86 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 86 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 86 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_87 : ∀ b, b < 97 →
    (fastOk E1 E2 512 87 b &&
      ((fastAnswer E1 E2 W2 512 87 b == (87 + b) % 97) == !(wrongRows.getD 87 []).contains b)) = true := by
  decide +kernel

/-- Row 87: the network answers (87 + b) % 97 exactly for the b outside row 87 of `wrongRows`. -/
theorem row_87 : ∀ b, b < 97 → (answer 87 b = (87 + b) % 97 ↔ b ∉ wrongRows.getD 87 []) := by
  intro b hb
  have h := fast_87 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 87 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 87 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H512_lr002_s0_step1.ClockBias

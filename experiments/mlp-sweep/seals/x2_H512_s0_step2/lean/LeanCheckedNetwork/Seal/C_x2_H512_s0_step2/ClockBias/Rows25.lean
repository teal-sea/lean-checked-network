import LeanCheckedNetwork.Seal.C_x2_H512_s0_step2.ClockBias.Table

/-! Rows 76 to 78 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H512_s0_step2.ClockBias

open LeanCheckedNetwork

theorem fast_76 : ∀ b, b < 97 →
    (fastOk E1 E2 512 76 b &&
      ((fastAnswer E1 E2 W2 512 76 b == (76 + b) % 97) == !(wrongRows.getD 76 []).contains b)) = true := by
  decide +kernel

/-- Row 76: the network answers (76 + b) % 97 exactly for the b outside row 76 of `wrongRows`. -/
theorem row_76 : ∀ b, b < 97 → (answer 76 b = (76 + b) % 97 ↔ b ∉ wrongRows.getD 76 []) := by
  intro b hb
  have h := fast_76 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 76 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 76 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_77 : ∀ b, b < 97 →
    (fastOk E1 E2 512 77 b &&
      ((fastAnswer E1 E2 W2 512 77 b == (77 + b) % 97) == !(wrongRows.getD 77 []).contains b)) = true := by
  decide +kernel

/-- Row 77: the network answers (77 + b) % 97 exactly for the b outside row 77 of `wrongRows`. -/
theorem row_77 : ∀ b, b < 97 → (answer 77 b = (77 + b) % 97 ↔ b ∉ wrongRows.getD 77 []) := by
  intro b hb
  have h := fast_77 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 77 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 77 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_78 : ∀ b, b < 97 →
    (fastOk E1 E2 512 78 b &&
      ((fastAnswer E1 E2 W2 512 78 b == (78 + b) % 97) == !(wrongRows.getD 78 []).contains b)) = true := by
  decide +kernel

/-- Row 78: the network answers (78 + b) % 97 exactly for the b outside row 78 of `wrongRows`. -/
theorem row_78 : ∀ b, b < 97 → (answer 78 b = (78 + b) % 97 ↔ b ∉ wrongRows.getD 78 []) := by
  intro b hb
  have h := fast_78 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 78 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 78 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H512_s0_step2.ClockBias

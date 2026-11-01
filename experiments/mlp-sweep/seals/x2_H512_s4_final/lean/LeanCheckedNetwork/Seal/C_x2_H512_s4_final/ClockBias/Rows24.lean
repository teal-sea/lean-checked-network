import LeanCheckedNetwork.Seal.C_x2_H512_s4_final.ClockBias.Table

/-! Rows 73 to 75 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H512_s4_final.ClockBias

open LeanCheckedNetwork

theorem fast_73 : ∀ b, b < 97 →
    (fastOk E1 E2 512 73 b &&
      ((fastAnswer E1 E2 W2 512 73 b == (73 + b) % 97) == !(wrongRows.getD 73 []).contains b)) = true := by
  decide +kernel

/-- Row 73: the network answers (73 + b) % 97 exactly for the b outside row 73 of `wrongRows`. -/
theorem row_73 : ∀ b, b < 97 → (answer 73 b = (73 + b) % 97 ↔ b ∉ wrongRows.getD 73 []) := by
  intro b hb
  have h := fast_73 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 73 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 73 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_74 : ∀ b, b < 97 →
    (fastOk E1 E2 512 74 b &&
      ((fastAnswer E1 E2 W2 512 74 b == (74 + b) % 97) == !(wrongRows.getD 74 []).contains b)) = true := by
  decide +kernel

/-- Row 74: the network answers (74 + b) % 97 exactly for the b outside row 74 of `wrongRows`. -/
theorem row_74 : ∀ b, b < 97 → (answer 74 b = (74 + b) % 97 ↔ b ∉ wrongRows.getD 74 []) := by
  intro b hb
  have h := fast_74 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 74 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 74 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_75 : ∀ b, b < 97 →
    (fastOk E1 E2 512 75 b &&
      ((fastAnswer E1 E2 W2 512 75 b == (75 + b) % 97) == !(wrongRows.getD 75 []).contains b)) = true := by
  decide +kernel

/-- Row 75: the network answers (75 + b) % 97 exactly for the b outside row 75 of `wrongRows`. -/
theorem row_75 : ∀ b, b < 97 → (answer 75 b = (75 + b) % 97 ↔ b ∉ wrongRows.getD 75 []) := by
  intro b hb
  have h := fast_75 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 75 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 512 75 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H512_s4_final.ClockBias

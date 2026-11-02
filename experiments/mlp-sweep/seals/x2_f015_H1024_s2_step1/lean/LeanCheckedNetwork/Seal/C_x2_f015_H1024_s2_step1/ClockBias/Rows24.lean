import LeanCheckedNetwork.Seal.C_x2_f015_H1024_s2_step1.ClockBias.Table

/-! Rows 48 to 49 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_f015_H1024_s2_step1.ClockBias

open LeanCheckedNetwork

theorem fast_48 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 48 b &&
      ((fastAnswer E1 E2 W2 1024 48 b == (48 + b) % 97) == !(wrongRows.getD 48 []).contains b)) = true := by
  decide +kernel

/-- Row 48: the network answers (48 + b) % 97 exactly for the b outside row 48 of `wrongRows`. -/
theorem row_48 : ∀ b, b < 97 → (answer 48 b = (48 + b) % 97 ↔ b ∉ wrongRows.getD 48 []) := by
  intro b hb
  have h := fast_48 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 48 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 48 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_49 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 49 b &&
      ((fastAnswer E1 E2 W2 1024 49 b == (49 + b) % 97) == !(wrongRows.getD 49 []).contains b)) = true := by
  decide +kernel

/-- Row 49: the network answers (49 + b) % 97 exactly for the b outside row 49 of `wrongRows`. -/
theorem row_49 : ∀ b, b < 97 → (answer 49 b = (49 + b) % 97 ↔ b ∉ wrongRows.getD 49 []) := by
  intro b hb
  have h := fast_49 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 49 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 49 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_f015_H1024_s2_step1.ClockBias

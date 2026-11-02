import LeanCheckedNetwork.Seal.C_x2_f015_H1024_s2_step1.ClockBias.Table

/-! Rows 2 to 3 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_f015_H1024_s2_step1.ClockBias

open LeanCheckedNetwork

theorem fast_2 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 2 b &&
      ((fastAnswer E1 E2 W2 1024 2 b == (2 + b) % 97) == !(wrongRows.getD 2 []).contains b)) = true := by
  decide +kernel

/-- Row 2: the network answers (2 + b) % 97 exactly for the b outside row 2 of `wrongRows`. -/
theorem row_2 : ∀ b, b < 97 → (answer 2 b = (2 + b) % 97 ↔ b ∉ wrongRows.getD 2 []) := by
  intro b hb
  have h := fast_2 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 2 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 2 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_3 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 3 b &&
      ((fastAnswer E1 E2 W2 1024 3 b == (3 + b) % 97) == !(wrongRows.getD 3 []).contains b)) = true := by
  decide +kernel

/-- Row 3: the network answers (3 + b) % 97 exactly for the b outside row 3 of `wrongRows`. -/
theorem row_3 : ∀ b, b < 97 → (answer 3 b = (3 + b) % 97 ↔ b ∉ wrongRows.getD 3 []) := by
  intro b hb
  have h := fast_3 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 3 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 3 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_f015_H1024_s2_step1.ClockBias

import LeanCheckedNetwork.Seal.C_x2_f015_H1024_s2_step1.Trained.Table

/-! Rows 44 to 45 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_f015_H1024_s2_step1.Trained

open LeanCheckedNetwork

theorem fast_44 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 44 b &&
      ((fastAnswer E1 E2 W2 1024 44 b == (44 + b) % 97) == !(wrongRows.getD 44 []).contains b)) = true := by
  decide +kernel

/-- Row 44: the network answers (44 + b) % 97 exactly for the b outside row 44 of `wrongRows`. -/
theorem row_44 : ∀ b, b < 97 → (answer 44 b = (44 + b) % 97 ↔ b ∉ wrongRows.getD 44 []) := by
  intro b hb
  have h := fast_44 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 44 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 44 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_45 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 45 b &&
      ((fastAnswer E1 E2 W2 1024 45 b == (45 + b) % 97) == !(wrongRows.getD 45 []).contains b)) = true := by
  decide +kernel

/-- Row 45: the network answers (45 + b) % 97 exactly for the b outside row 45 of `wrongRows`. -/
theorem row_45 : ∀ b, b < 97 → (answer 45 b = (45 + b) % 97 ↔ b ∉ wrongRows.getD 45 []) := by
  intro b hb
  have h := fast_45 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 45 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 45 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_f015_H1024_s2_step1.Trained

import LeanCheckedNetwork.Seal.C_x2_f010_H1024_s2_step2.Trained.Table

/-! Rows 64 to 65 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_f010_H1024_s2_step2.Trained

open LeanCheckedNetwork

theorem fast_64 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 64 b &&
      ((fastAnswer E1 E2 W2 1024 64 b == (64 + b) % 97) == !(wrongRows.getD 64 []).contains b)) = true := by
  decide +kernel

/-- Row 64: the network answers (64 + b) % 97 exactly for the b outside row 64 of `wrongRows`. -/
theorem row_64 : ∀ b, b < 97 → (answer 64 b = (64 + b) % 97 ↔ b ∉ wrongRows.getD 64 []) := by
  intro b hb
  have h := fast_64 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 64 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 64 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_65 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 65 b &&
      ((fastAnswer E1 E2 W2 1024 65 b == (65 + b) % 97) == !(wrongRows.getD 65 []).contains b)) = true := by
  decide +kernel

/-- Row 65: the network answers (65 + b) % 97 exactly for the b outside row 65 of `wrongRows`. -/
theorem row_65 : ∀ b, b < 97 → (answer 65 b = (65 + b) % 97 ↔ b ∉ wrongRows.getD 65 []) := by
  intro b hb
  have h := fast_65 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 65 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 65 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_f010_H1024_s2_step2.Trained

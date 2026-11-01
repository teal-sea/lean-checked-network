import LeanCheckedNetwork.Seal.C_x2_H1024_s0_step1.Trained.Table

/-! Rows 83 to 83 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H1024_s0_step1.Trained

open LeanCheckedNetwork

theorem fast_83 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 83 b &&
      ((fastAnswer E1 E2 W2 1024 83 b == (83 + b) % 97) == !(wrongRows.getD 83 []).contains b)) = true := by
  decide +kernel

/-- Row 83: the network answers (83 + b) % 97 exactly for the b outside row 83 of `wrongRows`. -/
theorem row_83 : ∀ b, b < 97 → (answer 83 b = (83 + b) % 97 ↔ b ∉ wrongRows.getD 83 []) := by
  intro b hb
  have h := fast_83 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 83 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 83 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H1024_s0_step1.Trained

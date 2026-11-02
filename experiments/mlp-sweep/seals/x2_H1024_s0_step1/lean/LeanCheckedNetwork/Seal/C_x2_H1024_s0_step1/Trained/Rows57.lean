import LeanCheckedNetwork.Seal.C_x2_H1024_s0_step1.Trained.Table

/-! Rows 90 to 90 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H1024_s0_step1.Trained

open LeanCheckedNetwork

theorem fast_90 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 90 b &&
      ((fastAnswer E1 E2 W2 1024 90 b == (90 + b) % 97) == !(wrongRows.getD 90 []).contains b)) = true := by
  decide +kernel

/-- Row 90: the network answers (90 + b) % 97 exactly for the b outside row 90 of `wrongRows`. -/
theorem row_90 : ∀ b, b < 97 → (answer 90 b = (90 + b) % 97 ↔ b ∉ wrongRows.getD 90 []) := by
  intro b hb
  have h := fast_90 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 90 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 90 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H1024_s0_step1.Trained

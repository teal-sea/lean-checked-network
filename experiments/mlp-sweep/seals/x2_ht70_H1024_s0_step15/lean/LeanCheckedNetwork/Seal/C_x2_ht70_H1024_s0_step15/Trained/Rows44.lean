import LeanCheckedNetwork.Seal.C_x2_ht70_H1024_s0_step15.Trained.Table

/-! Rows 77 to 77 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_ht70_H1024_s0_step15.Trained

open LeanCheckedNetwork

theorem fast_77 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 77 b &&
      ((fastAnswer E1 E2 W2 1024 77 b == (77 + b) % 97) == !(wrongRows.getD 77 []).contains b)) = true := by
  decide +kernel

/-- Row 77: the network answers (77 + b) % 97 exactly for the b outside row 77 of `wrongRows`. -/
theorem row_77 : ∀ b, b < 97 → (answer 77 b = (77 + b) % 97 ↔ b ∉ wrongRows.getD 77 []) := by
  intro b hb
  have h := fast_77 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 77 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 77 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_ht70_H1024_s0_step15.Trained

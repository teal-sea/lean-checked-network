import LeanCheckedNetwork.Seal.C_x2_ht30_H1024_s0_step2.Trained.Table

/-! Rows 71 to 71 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_ht30_H1024_s0_step2.Trained

open LeanCheckedNetwork

theorem fast_71 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 71 b &&
      ((fastAnswer E1 E2 W2 1024 71 b == (71 + b) % 97) == !(wrongRows.getD 71 []).contains b)) = true := by
  decide +kernel

/-- Row 71: the network answers (71 + b) % 97 exactly for the b outside row 71 of `wrongRows`. -/
theorem row_71 : ∀ b, b < 97 → (answer 71 b = (71 + b) % 97 ↔ b ∉ wrongRows.getD 71 []) := by
  intro b hb
  have h := fast_71 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 71 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 71 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_ht30_H1024_s0_step2.Trained

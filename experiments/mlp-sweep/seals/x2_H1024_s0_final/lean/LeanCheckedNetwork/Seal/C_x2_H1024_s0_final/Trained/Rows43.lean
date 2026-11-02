import LeanCheckedNetwork.Seal.C_x2_H1024_s0_final.Trained.Table

/-! Rows 76 to 76 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_H1024_s0_final.Trained

open LeanCheckedNetwork

theorem fast_76 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 76 b &&
      ((fastAnswer E1 E2 W2 1024 76 b == (76 + b) % 97) == !(wrongRows.getD 76 []).contains b)) = true := by
  decide +kernel

/-- Row 76: the network answers (76 + b) % 97 exactly for the b outside row 76 of `wrongRows`. -/
theorem row_76 : ∀ b, b < 97 → (answer 76 b = (76 + b) % 97 ↔ b ∉ wrongRows.getD 76 []) := by
  intro b hb
  have h := fast_76 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 76 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 76 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_H1024_s0_final.Trained

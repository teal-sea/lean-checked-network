import LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.Trained.Table

/-! Rows 78 to 78 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.Trained

open LeanCheckedNetwork

theorem fast_78 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 78 b &&
      ((fastAnswer E1 E2 W2 1024 78 b == (78 + b) % 97) == !(wrongRows.getD 78 []).contains b)) = true := by
  decide +kernel

/-- Row 78: the network answers (78 + b) % 97 exactly for the b outside row 78 of `wrongRows`. -/
theorem row_78 : ∀ b, b < 97 → (answer 78 b = (78 + b) % 97 ↔ b ∉ wrongRows.getD 78 []) := by
  intro b hb
  have h := fast_78 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 78 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 78 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.Trained

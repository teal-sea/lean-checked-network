import LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.Trained.Table

/-! Rows 85 to 85 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.Trained

open LeanCheckedNetwork

theorem fast_85 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 85 b &&
      ((fastAnswer E1 E2 W2 1024 85 b == (85 + b) % 97) == !(wrongRows.getD 85 []).contains b)) = true := by
  decide +kernel

/-- Row 85: the network answers (85 + b) % 97 exactly for the b outside row 85 of `wrongRows`. -/
theorem row_85 : ∀ b, b < 97 → (answer 85 b = (85 + b) % 97 ↔ b ∉ wrongRows.getD 85 []) := by
  intro b hb
  have h := fast_85 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 85 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 85 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.Trained

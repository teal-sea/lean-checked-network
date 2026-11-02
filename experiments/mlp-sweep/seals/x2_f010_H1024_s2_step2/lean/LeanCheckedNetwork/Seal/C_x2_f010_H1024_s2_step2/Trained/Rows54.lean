import LeanCheckedNetwork.Seal.C_x2_f010_H1024_s2_step2.Trained.Table

/-! Rows 87 to 87 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_f010_H1024_s2_step2.Trained

open LeanCheckedNetwork

theorem fast_87 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 87 b &&
      ((fastAnswer E1 E2 W2 1024 87 b == (87 + b) % 97) == !(wrongRows.getD 87 []).contains b)) = true := by
  decide +kernel

/-- Row 87: the network answers (87 + b) % 97 exactly for the b outside row 87 of `wrongRows`. -/
theorem row_87 : ∀ b, b < 97 → (answer 87 b = (87 + b) % 97 ↔ b ∉ wrongRows.getD 87 []) := by
  intro b hb
  have h := fast_87 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 87 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 87 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_f010_H1024_s2_step2.Trained

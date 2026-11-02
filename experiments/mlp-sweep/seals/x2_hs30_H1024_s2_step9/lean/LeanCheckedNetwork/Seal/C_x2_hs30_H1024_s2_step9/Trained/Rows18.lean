import LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.Trained.Table

/-! Rows 36 to 37 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.Trained

open LeanCheckedNetwork

theorem fast_36 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 36 b &&
      ((fastAnswer E1 E2 W2 1024 36 b == (36 + b) % 97) == !(wrongRows.getD 36 []).contains b)) = true := by
  decide +kernel

/-- Row 36: the network answers (36 + b) % 97 exactly for the b outside row 36 of `wrongRows`. -/
theorem row_36 : ∀ b, b < 97 → (answer 36 b = (36 + b) % 97 ↔ b ∉ wrongRows.getD 36 []) := by
  intro b hb
  have h := fast_36 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 36 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 36 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_37 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 37 b &&
      ((fastAnswer E1 E2 W2 1024 37 b == (37 + b) % 97) == !(wrongRows.getD 37 []).contains b)) = true := by
  decide +kernel

/-- Row 37: the network answers (37 + b) % 97 exactly for the b outside row 37 of `wrongRows`. -/
theorem row_37 : ∀ b, b < 97 → (answer 37 b = (37 + b) % 97 ↔ b ∉ wrongRows.getD 37 []) := by
  intro b hb
  have h := fast_37 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 37 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 37 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_x2_hs30_H1024_s2_step9.Trained

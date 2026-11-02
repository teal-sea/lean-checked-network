import LeanCheckedNetwork.Seal.C_gelu_H1024_s0_final_readsq.Trained.Table

/-! Rows 8 to 9 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_gelu_H1024_s0_final_readsq.Trained

open LeanCheckedNetwork

theorem fast_8 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 8 b &&
      ((fastAnswer E1 E2 W2 1024 8 b == (8 + b) % 97) == !(wrongRows.getD 8 []).contains b)) = true := by
  decide +kernel

/-- Row 8: the network answers (8 + b) % 97 exactly for the b outside row 8 of `wrongRows`. -/
theorem row_8 : ∀ b, b < 97 → (answer 8 b = (8 + b) % 97 ↔ b ∉ wrongRows.getD 8 []) := by
  intro b hb
  have h := fast_8 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 8 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 8 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_9 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 9 b &&
      ((fastAnswer E1 E2 W2 1024 9 b == (9 + b) % 97) == !(wrongRows.getD 9 []).contains b)) = true := by
  decide +kernel

/-- Row 9: the network answers (9 + b) % 97 exactly for the b outside row 9 of `wrongRows`. -/
theorem row_9 : ∀ b, b < 97 → (answer 9 b = (9 + b) % 97 ↔ b ∉ wrongRows.getD 9 []) := by
  intro b hb
  have h := fast_9 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 9 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 9 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_gelu_H1024_s0_final_readsq.Trained

import LeanCheckedNetwork.Seal.C_gelu_H1024_s0_final_readsq.Trained.Table

/-! Rows 26 to 27 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_gelu_H1024_s0_final_readsq.Trained

open LeanCheckedNetwork

theorem fast_26 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 26 b &&
      ((fastAnswer E1 E2 W2 1024 26 b == (26 + b) % 97) == !(wrongRows.getD 26 []).contains b)) = true := by
  decide +kernel

/-- Row 26: the network answers (26 + b) % 97 exactly for the b outside row 26 of `wrongRows`. -/
theorem row_26 : ∀ b, b < 97 → (answer 26 b = (26 + b) % 97 ↔ b ∉ wrongRows.getD 26 []) := by
  intro b hb
  have h := fast_26 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 26 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 26 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_27 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 27 b &&
      ((fastAnswer E1 E2 W2 1024 27 b == (27 + b) % 97) == !(wrongRows.getD 27 []).contains b)) = true := by
  decide +kernel

/-- Row 27: the network answers (27 + b) % 97 exactly for the b outside row 27 of `wrongRows`. -/
theorem row_27 : ∀ b, b < 97 → (answer 27 b = (27 + b) % 97 ↔ b ∉ wrongRows.getD 27 []) := by
  intro b hb
  have h := fast_27 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 27 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 27 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_gelu_H1024_s0_final_readsq.Trained

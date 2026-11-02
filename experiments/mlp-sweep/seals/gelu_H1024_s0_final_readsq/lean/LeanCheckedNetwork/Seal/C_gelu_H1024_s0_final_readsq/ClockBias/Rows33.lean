import LeanCheckedNetwork.Seal.C_gelu_H1024_s0_final_readsq.ClockBias.Table

/-! Rows 66 to 66 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_gelu_H1024_s0_final_readsq.ClockBias

open LeanCheckedNetwork

theorem fast_66 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 66 b &&
      ((fastAnswer E1 E2 W2 1024 66 b == (66 + b) % 97) == !(wrongRows.getD 66 []).contains b)) = true := by
  decide +kernel

/-- Row 66: the network answers (66 + b) % 97 exactly for the b outside row 66 of `wrongRows`. -/
theorem row_66 : ∀ b, b < 97 → (answer 66 b = (66 + b) % 97 ↔ b ∉ wrongRows.getD 66 []) := by
  intro b hb
  have h := fast_66 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 66 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 66 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_gelu_H1024_s0_final_readsq.ClockBias

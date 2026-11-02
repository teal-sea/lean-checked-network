import LeanCheckedNetwork.Seal.C_silu_H1024_s0_step2000_readsq.ClockBias.Table

/-! Rows 69 to 69 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_silu_H1024_s0_step2000_readsq.ClockBias

open LeanCheckedNetwork

theorem fast_69 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 69 b &&
      ((fastAnswer E1 E2 W2 1024 69 b == (69 + b) % 97) == !(wrongRows.getD 69 []).contains b)) = true := by
  decide +kernel

/-- Row 69: the network answers (69 + b) % 97 exactly for the b outside row 69 of `wrongRows`. -/
theorem row_69 : ∀ b, b < 97 → (answer 69 b = (69 + b) % 97 ↔ b ∉ wrongRows.getD 69 []) := by
  intro b hb
  have h := fast_69 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 69 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 69 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_silu_H1024_s0_step2000_readsq.ClockBias

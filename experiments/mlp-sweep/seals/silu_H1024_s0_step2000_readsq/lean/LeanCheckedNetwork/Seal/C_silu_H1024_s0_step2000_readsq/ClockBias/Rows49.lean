import LeanCheckedNetwork.Seal.C_silu_H1024_s0_step2000_readsq.ClockBias.Table

/-! Rows 82 to 82 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_silu_H1024_s0_step2000_readsq.ClockBias

open LeanCheckedNetwork

theorem fast_82 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 82 b &&
      ((fastAnswer E1 E2 W2 1024 82 b == (82 + b) % 97) == !(wrongRows.getD 82 []).contains b)) = true := by
  decide +kernel

/-- Row 82: the network answers (82 + b) % 97 exactly for the b outside row 82 of `wrongRows`. -/
theorem row_82 : ∀ b, b < 97 → (answer 82 b = (82 + b) % 97 ↔ b ∉ wrongRows.getD 82 []) := by
  intro b hb
  have h := fast_82 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 82 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 82 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_silu_H1024_s0_step2000_readsq.ClockBias

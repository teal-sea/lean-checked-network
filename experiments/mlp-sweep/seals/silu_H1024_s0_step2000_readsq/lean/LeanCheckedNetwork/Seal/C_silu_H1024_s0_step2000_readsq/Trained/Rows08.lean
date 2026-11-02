import LeanCheckedNetwork.Seal.C_silu_H1024_s0_step2000_readsq.Trained.Table

/-! Rows 16 to 17 of the addition table, checked by Lean's kernel for all 97 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Seal.C_silu_H1024_s0_step2000_readsq.Trained

open LeanCheckedNetwork

theorem fast_16 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 16 b &&
      ((fastAnswer E1 E2 W2 1024 16 b == (16 + b) % 97) == !(wrongRows.getD 16 []).contains b)) = true := by
  decide +kernel

/-- Row 16: the network answers (16 + b) % 97 exactly for the b outside row 16 of `wrongRows`. -/
theorem row_16 : ∀ b, b < 97 → (answer 16 b = (16 + b) % 97 ↔ b ∉ wrongRows.getD 16 []) := by
  intro b hb
  have h := fast_16 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 16 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 16 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

theorem fast_17 : ∀ b, b < 97 →
    (fastOk E1 E2 1024 17 b &&
      ((fastAnswer E1 E2 W2 1024 17 b == (17 + b) % 97) == !(wrongRows.getD 17 []).contains b)) = true := by
  decide +kernel

/-- Row 17: the network answers (17 + b) % 97 exactly for the b outside row 17 of `wrongRows`. -/
theorem row_17 : ∀ b, b < 97 → (answer 17 b = (17 + b) % 97 ↔ b ∉ wrongRows.getD 17 []) := by
  intro b hb
  have h := fast_17 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 17 b = _ ↔ _
  rw [answer_eq_fastAnswer E1 E2 W2 1024 17 b table_ok h.1]
  exact iff_not_mem_of_beq h.2

end LeanCheckedNetwork.Seal.C_silu_H1024_s0_step2000_readsq.Trained

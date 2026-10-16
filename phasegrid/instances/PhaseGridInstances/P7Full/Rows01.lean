import PhaseGridInstances.P7Full.Table

/-! Rows 4 to 6 of the addition table, checked by Lean's kernel for all 7 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P7Full

open LeanCheckedNetwork

theorem fast_4 : ∀ b, b < 7 →
    (fastOk E1 E2 24 4 b && fastAnswer E1 E2 W2 24 4 b == (4 + b) % 7) = true := by
  decide +kernel

/-- Row 4 of the addition table: the network answers (4 + b) % 7 for every b. -/
theorem row_4 : ∀ b, b < 7 → answer 4 b = (4 + b) % 7 := by
  intro b hb
  have h := fast_4 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 4 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 24 4 b table_ok h.1, h.2]

theorem fast_5 : ∀ b, b < 7 →
    (fastOk E1 E2 24 5 b && fastAnswer E1 E2 W2 24 5 b == (5 + b) % 7) = true := by
  decide +kernel

/-- Row 5 of the addition table: the network answers (5 + b) % 7 for every b. -/
theorem row_5 : ∀ b, b < 7 → answer 5 b = (5 + b) % 7 := by
  intro b hb
  have h := fast_5 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 5 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 24 5 b table_ok h.1, h.2]

theorem fast_6 : ∀ b, b < 7 →
    (fastOk E1 E2 24 6 b && fastAnswer E1 E2 W2 24 6 b == (6 + b) % 7) = true := by
  decide +kernel

/-- Row 6 of the addition table: the network answers (6 + b) % 7 for every b. -/
theorem row_6 : ∀ b, b < 7 → answer 6 b = (6 + b) % 7 := by
  intro b hb
  have h := fast_6 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 6 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 24 6 b table_ok h.1, h.2]

end PhaseGridInstances.P7Full

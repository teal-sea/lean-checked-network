import LeanCheckedNetwork.Mod12All.Table

/-! Rows 9 to 11 of the addition table, checked by Lean's kernel for all 12 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod12All

open LeanCheckedNetwork

theorem fast_9 : ∀ b, b < 12 →
    (fastOk E1 E2 40 9 b && fastAnswer E1 E2 W2 40 9 b == (9 + b) % 12) = true := by
  decide +kernel

/-- Row 9 of the addition table: the network answers (9 + b) % 12 for every b. -/
theorem row_9 : ∀ b, b < 12 → answer 9 b = (9 + b) % 12 := by
  intro b hb
  have h := fast_9 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 9 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 9 b table_ok h.1, h.2]

theorem fast_10 : ∀ b, b < 12 →
    (fastOk E1 E2 40 10 b && fastAnswer E1 E2 W2 40 10 b == (10 + b) % 12) = true := by
  decide +kernel

/-- Row 10 of the addition table: the network answers (10 + b) % 12 for every b. -/
theorem row_10 : ∀ b, b < 12 → answer 10 b = (10 + b) % 12 := by
  intro b hb
  have h := fast_10 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 10 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 10 b table_ok h.1, h.2]

theorem fast_11 : ∀ b, b < 12 →
    (fastOk E1 E2 40 11 b && fastAnswer E1 E2 W2 40 11 b == (11 + b) % 12) = true := by
  decide +kernel

/-- Row 11 of the addition table: the network answers (11 + b) % 12 for every b. -/
theorem row_11 : ∀ b, b < 12 → answer 11 b = (11 + b) % 12 := by
  intro b hb
  have h := fast_11 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 11 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 11 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod12All

import LeanCheckedNetwork.Mod12All.Table

/-! Rows 0 to 2 of the addition table, checked by Lean's kernel for all 12 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod12All

open LeanCheckedNetwork

theorem fast_0 : ∀ b, b < 12 →
    (fastOk E1 E2 40 0 b && fastAnswer E1 E2 W2 40 0 b == (0 + b) % 12) = true := by
  decide +kernel

/-- Row 0 of the addition table: the network answers (0 + b) % 12 for every b. -/
theorem row_0 : ∀ b, b < 12 → answer 0 b = (0 + b) % 12 := by
  intro b hb
  have h := fast_0 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 0 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 0 b table_ok h.1, h.2]

theorem fast_1 : ∀ b, b < 12 →
    (fastOk E1 E2 40 1 b && fastAnswer E1 E2 W2 40 1 b == (1 + b) % 12) = true := by
  decide +kernel

/-- Row 1 of the addition table: the network answers (1 + b) % 12 for every b. -/
theorem row_1 : ∀ b, b < 12 → answer 1 b = (1 + b) % 12 := by
  intro b hb
  have h := fast_1 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 1 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 1 b table_ok h.1, h.2]

theorem fast_2 : ∀ b, b < 12 →
    (fastOk E1 E2 40 2 b && fastAnswer E1 E2 W2 40 2 b == (2 + b) % 12) = true := by
  decide +kernel

/-- Row 2 of the addition table: the network answers (2 + b) % 12 for every b. -/
theorem row_2 : ∀ b, b < 12 → answer 2 b = (2 + b) % 12 := by
  intro b hb
  have h := fast_2 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 2 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 2 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod12All

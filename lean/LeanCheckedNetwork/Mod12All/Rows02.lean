import LeanCheckedNetwork.Mod12All.Table

/-! Rows 6 to 8 of the addition table, checked by Lean's kernel for all 12 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod12All

open LeanCheckedNetwork

theorem fast_6 : ∀ b, b < 12 →
    (fastOk E1 E2 40 6 b && fastAnswer E1 E2 W2 40 6 b == (6 + b) % 12) = true := by
  decide +kernel

/-- Row 6 of the addition table: the network answers (6 + b) % 12 for every b. -/
theorem row_6 : ∀ b, b < 12 → answer 6 b = (6 + b) % 12 := by
  intro b hb
  have h := fast_6 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 6 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 6 b table_ok h.1, h.2]

theorem fast_7 : ∀ b, b < 12 →
    (fastOk E1 E2 40 7 b && fastAnswer E1 E2 W2 40 7 b == (7 + b) % 12) = true := by
  decide +kernel

/-- Row 7 of the addition table: the network answers (7 + b) % 12 for every b. -/
theorem row_7 : ∀ b, b < 12 → answer 7 b = (7 + b) % 12 := by
  intro b hb
  have h := fast_7 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 7 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 7 b table_ok h.1, h.2]

theorem fast_8 : ∀ b, b < 12 →
    (fastOk E1 E2 40 8 b && fastAnswer E1 E2 W2 40 8 b == (8 + b) % 12) = true := by
  decide +kernel

/-- Row 8 of the addition table: the network answers (8 + b) % 12 for every b. -/
theorem row_8 : ∀ b, b < 12 → answer 8 b = (8 + b) % 12 := by
  intro b hb
  have h := fast_8 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 8 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 8 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod12All

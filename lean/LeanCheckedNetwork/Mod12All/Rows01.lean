import LeanCheckedNetwork.Mod12All.Table

/-! Rows 3 to 5 of the addition table, checked by Lean's kernel for all 12 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod12All

open LeanCheckedNetwork

theorem fast_3 : ∀ b, b < 12 →
    (fastOk E1 E2 40 3 b && fastAnswer E1 E2 W2 40 3 b == (3 + b) % 12) = true := by
  decide +kernel

/-- Row 3 of the addition table: the network answers (3 + b) % 12 for every b. -/
theorem row_3 : ∀ b, b < 12 → answer 3 b = (3 + b) % 12 := by
  intro b hb
  have h := fast_3 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 3 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 3 b table_ok h.1, h.2]

theorem fast_4 : ∀ b, b < 12 →
    (fastOk E1 E2 40 4 b && fastAnswer E1 E2 W2 40 4 b == (4 + b) % 12) = true := by
  decide +kernel

/-- Row 4 of the addition table: the network answers (4 + b) % 12 for every b. -/
theorem row_4 : ∀ b, b < 12 → answer 4 b = (4 + b) % 12 := by
  intro b hb
  have h := fast_4 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 4 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 4 b table_ok h.1, h.2]

theorem fast_5 : ∀ b, b < 12 →
    (fastOk E1 E2 40 5 b && fastAnswer E1 E2 W2 40 5 b == (5 + b) % 12) = true := by
  decide +kernel

/-- Row 5 of the addition table: the network answers (5 + b) % 12 for every b. -/
theorem row_5 : ∀ b, b < 12 → answer 5 b = (5 + b) % 12 := by
  intro b hb
  have h := fast_5 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 5 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 5 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod12All

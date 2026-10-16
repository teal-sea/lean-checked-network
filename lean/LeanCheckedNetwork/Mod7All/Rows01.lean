import LeanCheckedNetwork.Mod7All.Table

/-! Rows 2 to 3 of the addition table, checked by Lean's kernel for all 7 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod7All

open LeanCheckedNetwork

theorem fast_2 : ∀ b, b < 7 →
    (fastOk E1 E2 24 2 b && fastAnswer E1 E2 W2 24 2 b == (2 + b) % 7) = true := by
  decide +kernel

/-- Row 2 of the addition table: the network answers (2 + b) % 7 for every b. -/
theorem row_2 : ∀ b, b < 7 → answer 2 b = (2 + b) % 7 := by
  intro b hb
  have h := fast_2 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 2 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 24 2 b table_ok h.1, h.2]

theorem fast_3 : ∀ b, b < 7 →
    (fastOk E1 E2 24 3 b && fastAnswer E1 E2 W2 24 3 b == (3 + b) % 7) = true := by
  decide +kernel

/-- Row 3 of the addition table: the network answers (3 + b) % 7 for every b. -/
theorem row_3 : ∀ b, b < 7 → answer 3 b = (3 + b) % 7 := by
  intro b hb
  have h := fast_3 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 3 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 24 3 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod7All

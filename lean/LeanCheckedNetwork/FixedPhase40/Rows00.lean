import LeanCheckedNetwork.FixedPhase40.Table

/-! Rows 0 to 7 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.FixedPhase40

open LeanCheckedNetwork

theorem fast_0 : ∀ b, b < 113 →
    (fastOk E1 E2 40 0 b && fastAnswer E1 E2 W2 40 0 b == (0 + b) % 113) = true := by
  decide +kernel

/-- Row 0 of the addition table: the network answers (0 + b) % 113 for every b. -/
theorem row_0 : ∀ b, b < 113 → answer 0 b = (0 + b) % 113 := by
  intro b hb
  have h := fast_0 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 0 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 0 b table_ok h.1, h.2]

theorem fast_1 : ∀ b, b < 113 →
    (fastOk E1 E2 40 1 b && fastAnswer E1 E2 W2 40 1 b == (1 + b) % 113) = true := by
  decide +kernel

/-- Row 1 of the addition table: the network answers (1 + b) % 113 for every b. -/
theorem row_1 : ∀ b, b < 113 → answer 1 b = (1 + b) % 113 := by
  intro b hb
  have h := fast_1 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 1 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 1 b table_ok h.1, h.2]

theorem fast_2 : ∀ b, b < 113 →
    (fastOk E1 E2 40 2 b && fastAnswer E1 E2 W2 40 2 b == (2 + b) % 113) = true := by
  decide +kernel

/-- Row 2 of the addition table: the network answers (2 + b) % 113 for every b. -/
theorem row_2 : ∀ b, b < 113 → answer 2 b = (2 + b) % 113 := by
  intro b hb
  have h := fast_2 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 2 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 2 b table_ok h.1, h.2]

theorem fast_3 : ∀ b, b < 113 →
    (fastOk E1 E2 40 3 b && fastAnswer E1 E2 W2 40 3 b == (3 + b) % 113) = true := by
  decide +kernel

/-- Row 3 of the addition table: the network answers (3 + b) % 113 for every b. -/
theorem row_3 : ∀ b, b < 113 → answer 3 b = (3 + b) % 113 := by
  intro b hb
  have h := fast_3 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 3 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 3 b table_ok h.1, h.2]

theorem fast_4 : ∀ b, b < 113 →
    (fastOk E1 E2 40 4 b && fastAnswer E1 E2 W2 40 4 b == (4 + b) % 113) = true := by
  decide +kernel

/-- Row 4 of the addition table: the network answers (4 + b) % 113 for every b. -/
theorem row_4 : ∀ b, b < 113 → answer 4 b = (4 + b) % 113 := by
  intro b hb
  have h := fast_4 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 4 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 4 b table_ok h.1, h.2]

theorem fast_5 : ∀ b, b < 113 →
    (fastOk E1 E2 40 5 b && fastAnswer E1 E2 W2 40 5 b == (5 + b) % 113) = true := by
  decide +kernel

/-- Row 5 of the addition table: the network answers (5 + b) % 113 for every b. -/
theorem row_5 : ∀ b, b < 113 → answer 5 b = (5 + b) % 113 := by
  intro b hb
  have h := fast_5 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 5 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 5 b table_ok h.1, h.2]

theorem fast_6 : ∀ b, b < 113 →
    (fastOk E1 E2 40 6 b && fastAnswer E1 E2 W2 40 6 b == (6 + b) % 113) = true := by
  decide +kernel

/-- Row 6 of the addition table: the network answers (6 + b) % 113 for every b. -/
theorem row_6 : ∀ b, b < 113 → answer 6 b = (6 + b) % 113 := by
  intro b hb
  have h := fast_6 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 6 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 6 b table_ok h.1, h.2]

theorem fast_7 : ∀ b, b < 113 →
    (fastOk E1 E2 40 7 b && fastAnswer E1 E2 W2 40 7 b == (7 + b) % 113) = true := by
  decide +kernel

/-- Row 7 of the addition table: the network answers (7 + b) % 113 for every b. -/
theorem row_7 : ∀ b, b < 113 → answer 7 b = (7 + b) % 113 := by
  intro b hb
  have h := fast_7 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 7 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 7 b table_ok h.1, h.2]

end LeanCheckedNetwork.FixedPhase40

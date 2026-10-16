import LeanCheckedNetwork.FixedPhase12.Table

/-! Rows 8 to 14 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.FixedPhase12

open LeanCheckedNetwork

theorem fast_8 : ∀ b, b < 113 →
    (fastOk E1 E2 12 8 b && fastAnswer E1 E2 W2 12 8 b == (8 + b) % 113) = true := by
  decide +kernel

/-- Row 8 of the addition table: the network answers (8 + b) % 113 for every b. -/
theorem row_8 : ∀ b, b < 113 → answer 8 b = (8 + b) % 113 := by
  intro b hb
  have h := fast_8 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 8 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 8 b table_ok h.1, h.2]

theorem fast_9 : ∀ b, b < 113 →
    (fastOk E1 E2 12 9 b && fastAnswer E1 E2 W2 12 9 b == (9 + b) % 113) = true := by
  decide +kernel

/-- Row 9 of the addition table: the network answers (9 + b) % 113 for every b. -/
theorem row_9 : ∀ b, b < 113 → answer 9 b = (9 + b) % 113 := by
  intro b hb
  have h := fast_9 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 9 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 9 b table_ok h.1, h.2]

theorem fast_10 : ∀ b, b < 113 →
    (fastOk E1 E2 12 10 b && fastAnswer E1 E2 W2 12 10 b == (10 + b) % 113) = true := by
  decide +kernel

/-- Row 10 of the addition table: the network answers (10 + b) % 113 for every b. -/
theorem row_10 : ∀ b, b < 113 → answer 10 b = (10 + b) % 113 := by
  intro b hb
  have h := fast_10 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 10 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 10 b table_ok h.1, h.2]

theorem fast_11 : ∀ b, b < 113 →
    (fastOk E1 E2 12 11 b && fastAnswer E1 E2 W2 12 11 b == (11 + b) % 113) = true := by
  decide +kernel

/-- Row 11 of the addition table: the network answers (11 + b) % 113 for every b. -/
theorem row_11 : ∀ b, b < 113 → answer 11 b = (11 + b) % 113 := by
  intro b hb
  have h := fast_11 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 11 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 11 b table_ok h.1, h.2]

theorem fast_12 : ∀ b, b < 113 →
    (fastOk E1 E2 12 12 b && fastAnswer E1 E2 W2 12 12 b == (12 + b) % 113) = true := by
  decide +kernel

/-- Row 12 of the addition table: the network answers (12 + b) % 113 for every b. -/
theorem row_12 : ∀ b, b < 113 → answer 12 b = (12 + b) % 113 := by
  intro b hb
  have h := fast_12 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 12 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 12 b table_ok h.1, h.2]

theorem fast_13 : ∀ b, b < 113 →
    (fastOk E1 E2 12 13 b && fastAnswer E1 E2 W2 12 13 b == (13 + b) % 113) = true := by
  decide +kernel

/-- Row 13 of the addition table: the network answers (13 + b) % 113 for every b. -/
theorem row_13 : ∀ b, b < 113 → answer 13 b = (13 + b) % 113 := by
  intro b hb
  have h := fast_13 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 13 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 13 b table_ok h.1, h.2]

theorem fast_14 : ∀ b, b < 113 →
    (fastOk E1 E2 12 14 b && fastAnswer E1 E2 W2 12 14 b == (14 + b) % 113) = true := by
  decide +kernel

/-- Row 14 of the addition table: the network answers (14 + b) % 113 for every b. -/
theorem row_14 : ∀ b, b < 113 → answer 14 b = (14 + b) % 113 := by
  intro b hb
  have h := fast_14 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 14 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 14 b table_ok h.1, h.2]

end LeanCheckedNetwork.FixedPhase12

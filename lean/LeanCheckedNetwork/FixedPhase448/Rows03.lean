import LeanCheckedNetwork.FixedPhase448.Table

/-! Rows 22 to 28 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.FixedPhase448

open LeanCheckedNetwork

theorem fast_22 : ∀ b, b < 113 →
    (fastOk E1 E2 448 22 b && fastAnswer E1 E2 W2 448 22 b == (22 + b) % 113) = true := by
  decide +kernel

/-- Row 22 of the addition table: the network answers (22 + b) % 113 for every b. -/
theorem row_22 : ∀ b, b < 113 → answer 22 b = (22 + b) % 113 := by
  intro b hb
  have h := fast_22 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 22 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 22 b table_ok h.1, h.2]

theorem fast_23 : ∀ b, b < 113 →
    (fastOk E1 E2 448 23 b && fastAnswer E1 E2 W2 448 23 b == (23 + b) % 113) = true := by
  decide +kernel

/-- Row 23 of the addition table: the network answers (23 + b) % 113 for every b. -/
theorem row_23 : ∀ b, b < 113 → answer 23 b = (23 + b) % 113 := by
  intro b hb
  have h := fast_23 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 23 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 23 b table_ok h.1, h.2]

theorem fast_24 : ∀ b, b < 113 →
    (fastOk E1 E2 448 24 b && fastAnswer E1 E2 W2 448 24 b == (24 + b) % 113) = true := by
  decide +kernel

/-- Row 24 of the addition table: the network answers (24 + b) % 113 for every b. -/
theorem row_24 : ∀ b, b < 113 → answer 24 b = (24 + b) % 113 := by
  intro b hb
  have h := fast_24 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 24 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 24 b table_ok h.1, h.2]

theorem fast_25 : ∀ b, b < 113 →
    (fastOk E1 E2 448 25 b && fastAnswer E1 E2 W2 448 25 b == (25 + b) % 113) = true := by
  decide +kernel

/-- Row 25 of the addition table: the network answers (25 + b) % 113 for every b. -/
theorem row_25 : ∀ b, b < 113 → answer 25 b = (25 + b) % 113 := by
  intro b hb
  have h := fast_25 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 25 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 25 b table_ok h.1, h.2]

theorem fast_26 : ∀ b, b < 113 →
    (fastOk E1 E2 448 26 b && fastAnswer E1 E2 W2 448 26 b == (26 + b) % 113) = true := by
  decide +kernel

/-- Row 26 of the addition table: the network answers (26 + b) % 113 for every b. -/
theorem row_26 : ∀ b, b < 113 → answer 26 b = (26 + b) % 113 := by
  intro b hb
  have h := fast_26 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 26 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 26 b table_ok h.1, h.2]

theorem fast_27 : ∀ b, b < 113 →
    (fastOk E1 E2 448 27 b && fastAnswer E1 E2 W2 448 27 b == (27 + b) % 113) = true := by
  decide +kernel

/-- Row 27 of the addition table: the network answers (27 + b) % 113 for every b. -/
theorem row_27 : ∀ b, b < 113 → answer 27 b = (27 + b) % 113 := by
  intro b hb
  have h := fast_27 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 27 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 27 b table_ok h.1, h.2]

theorem fast_28 : ∀ b, b < 113 →
    (fastOk E1 E2 448 28 b && fastAnswer E1 E2 W2 448 28 b == (28 + b) % 113) = true := by
  decide +kernel

/-- Row 28 of the addition table: the network answers (28 + b) % 113 for every b. -/
theorem row_28 : ∀ b, b < 113 → answer 28 b = (28 + b) % 113 := by
  intro b hb
  have h := fast_28 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 28 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 28 b table_ok h.1, h.2]

end LeanCheckedNetwork.FixedPhase448

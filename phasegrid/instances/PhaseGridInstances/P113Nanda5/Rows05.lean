import PhaseGridInstances.P113Nanda5.Table

/-! Rows 36 to 42 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Nanda5

open LeanCheckedNetwork

theorem fast_36 : ∀ b, b < 113 →
    (fastOk E1 E2 40 36 b && fastAnswer E1 E2 W2 40 36 b == (36 + b) % 113) = true := by
  decide +kernel

/-- Row 36 of the addition table: the network answers (36 + b) % 113 for every b. -/
theorem row_36 : ∀ b, b < 113 → answer 36 b = (36 + b) % 113 := by
  intro b hb
  have h := fast_36 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 36 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 36 b table_ok h.1, h.2]

theorem fast_37 : ∀ b, b < 113 →
    (fastOk E1 E2 40 37 b && fastAnswer E1 E2 W2 40 37 b == (37 + b) % 113) = true := by
  decide +kernel

/-- Row 37 of the addition table: the network answers (37 + b) % 113 for every b. -/
theorem row_37 : ∀ b, b < 113 → answer 37 b = (37 + b) % 113 := by
  intro b hb
  have h := fast_37 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 37 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 37 b table_ok h.1, h.2]

theorem fast_38 : ∀ b, b < 113 →
    (fastOk E1 E2 40 38 b && fastAnswer E1 E2 W2 40 38 b == (38 + b) % 113) = true := by
  decide +kernel

/-- Row 38 of the addition table: the network answers (38 + b) % 113 for every b. -/
theorem row_38 : ∀ b, b < 113 → answer 38 b = (38 + b) % 113 := by
  intro b hb
  have h := fast_38 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 38 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 38 b table_ok h.1, h.2]

theorem fast_39 : ∀ b, b < 113 →
    (fastOk E1 E2 40 39 b && fastAnswer E1 E2 W2 40 39 b == (39 + b) % 113) = true := by
  decide +kernel

/-- Row 39 of the addition table: the network answers (39 + b) % 113 for every b. -/
theorem row_39 : ∀ b, b < 113 → answer 39 b = (39 + b) % 113 := by
  intro b hb
  have h := fast_39 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 39 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 39 b table_ok h.1, h.2]

theorem fast_40 : ∀ b, b < 113 →
    (fastOk E1 E2 40 40 b && fastAnswer E1 E2 W2 40 40 b == (40 + b) % 113) = true := by
  decide +kernel

/-- Row 40 of the addition table: the network answers (40 + b) % 113 for every b. -/
theorem row_40 : ∀ b, b < 113 → answer 40 b = (40 + b) % 113 := by
  intro b hb
  have h := fast_40 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 40 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 40 b table_ok h.1, h.2]

theorem fast_41 : ∀ b, b < 113 →
    (fastOk E1 E2 40 41 b && fastAnswer E1 E2 W2 40 41 b == (41 + b) % 113) = true := by
  decide +kernel

/-- Row 41 of the addition table: the network answers (41 + b) % 113 for every b. -/
theorem row_41 : ∀ b, b < 113 → answer 41 b = (41 + b) % 113 := by
  intro b hb
  have h := fast_41 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 41 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 41 b table_ok h.1, h.2]

theorem fast_42 : ∀ b, b < 113 →
    (fastOk E1 E2 40 42 b && fastAnswer E1 E2 W2 40 42 b == (42 + b) % 113) = true := by
  decide +kernel

/-- Row 42 of the addition table: the network answers (42 + b) % 113 for every b. -/
theorem row_42 : ∀ b, b < 113 → answer 42 b = (42 + b) % 113 := by
  intro b hb
  have h := fast_42 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 42 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 42 b table_ok h.1, h.2]

end PhaseGridInstances.P113Nanda5

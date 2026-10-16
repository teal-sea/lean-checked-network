import PhaseGridInstances.P113Nanda5.Table

/-! Rows 64 to 70 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Nanda5

open LeanCheckedNetwork

theorem fast_64 : ∀ b, b < 113 →
    (fastOk E1 E2 40 64 b && fastAnswer E1 E2 W2 40 64 b == (64 + b) % 113) = true := by
  decide +kernel

/-- Row 64 of the addition table: the network answers (64 + b) % 113 for every b. -/
theorem row_64 : ∀ b, b < 113 → answer 64 b = (64 + b) % 113 := by
  intro b hb
  have h := fast_64 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 64 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 64 b table_ok h.1, h.2]

theorem fast_65 : ∀ b, b < 113 →
    (fastOk E1 E2 40 65 b && fastAnswer E1 E2 W2 40 65 b == (65 + b) % 113) = true := by
  decide +kernel

/-- Row 65 of the addition table: the network answers (65 + b) % 113 for every b. -/
theorem row_65 : ∀ b, b < 113 → answer 65 b = (65 + b) % 113 := by
  intro b hb
  have h := fast_65 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 65 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 65 b table_ok h.1, h.2]

theorem fast_66 : ∀ b, b < 113 →
    (fastOk E1 E2 40 66 b && fastAnswer E1 E2 W2 40 66 b == (66 + b) % 113) = true := by
  decide +kernel

/-- Row 66 of the addition table: the network answers (66 + b) % 113 for every b. -/
theorem row_66 : ∀ b, b < 113 → answer 66 b = (66 + b) % 113 := by
  intro b hb
  have h := fast_66 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 66 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 66 b table_ok h.1, h.2]

theorem fast_67 : ∀ b, b < 113 →
    (fastOk E1 E2 40 67 b && fastAnswer E1 E2 W2 40 67 b == (67 + b) % 113) = true := by
  decide +kernel

/-- Row 67 of the addition table: the network answers (67 + b) % 113 for every b. -/
theorem row_67 : ∀ b, b < 113 → answer 67 b = (67 + b) % 113 := by
  intro b hb
  have h := fast_67 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 67 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 67 b table_ok h.1, h.2]

theorem fast_68 : ∀ b, b < 113 →
    (fastOk E1 E2 40 68 b && fastAnswer E1 E2 W2 40 68 b == (68 + b) % 113) = true := by
  decide +kernel

/-- Row 68 of the addition table: the network answers (68 + b) % 113 for every b. -/
theorem row_68 : ∀ b, b < 113 → answer 68 b = (68 + b) % 113 := by
  intro b hb
  have h := fast_68 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 68 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 68 b table_ok h.1, h.2]

theorem fast_69 : ∀ b, b < 113 →
    (fastOk E1 E2 40 69 b && fastAnswer E1 E2 W2 40 69 b == (69 + b) % 113) = true := by
  decide +kernel

/-- Row 69 of the addition table: the network answers (69 + b) % 113 for every b. -/
theorem row_69 : ∀ b, b < 113 → answer 69 b = (69 + b) % 113 := by
  intro b hb
  have h := fast_69 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 69 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 69 b table_ok h.1, h.2]

theorem fast_70 : ∀ b, b < 113 →
    (fastOk E1 E2 40 70 b && fastAnswer E1 E2 W2 40 70 b == (70 + b) % 113) = true := by
  decide +kernel

/-- Row 70 of the addition table: the network answers (70 + b) % 113 for every b. -/
theorem row_70 : ∀ b, b < 113 → answer 70 b = (70 + b) % 113 := by
  intro b hb
  have h := fast_70 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 70 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 70 b table_ok h.1, h.2]

end PhaseGridInstances.P113Nanda5

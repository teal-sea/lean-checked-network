import LeanCheckedNetwork.FixedPhase448.Table

/-! Rows 78 to 84 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.FixedPhase448

open LeanCheckedNetwork

theorem fast_78 : ∀ b, b < 113 →
    (fastOk E1 E2 448 78 b && fastAnswer E1 E2 W2 448 78 b == (78 + b) % 113) = true := by
  decide +kernel

/-- Row 78 of the addition table: the network answers (78 + b) % 113 for every b. -/
theorem row_78 : ∀ b, b < 113 → answer 78 b = (78 + b) % 113 := by
  intro b hb
  have h := fast_78 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 78 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 78 b table_ok h.1, h.2]

theorem fast_79 : ∀ b, b < 113 →
    (fastOk E1 E2 448 79 b && fastAnswer E1 E2 W2 448 79 b == (79 + b) % 113) = true := by
  decide +kernel

/-- Row 79 of the addition table: the network answers (79 + b) % 113 for every b. -/
theorem row_79 : ∀ b, b < 113 → answer 79 b = (79 + b) % 113 := by
  intro b hb
  have h := fast_79 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 79 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 79 b table_ok h.1, h.2]

theorem fast_80 : ∀ b, b < 113 →
    (fastOk E1 E2 448 80 b && fastAnswer E1 E2 W2 448 80 b == (80 + b) % 113) = true := by
  decide +kernel

/-- Row 80 of the addition table: the network answers (80 + b) % 113 for every b. -/
theorem row_80 : ∀ b, b < 113 → answer 80 b = (80 + b) % 113 := by
  intro b hb
  have h := fast_80 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 80 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 80 b table_ok h.1, h.2]

theorem fast_81 : ∀ b, b < 113 →
    (fastOk E1 E2 448 81 b && fastAnswer E1 E2 W2 448 81 b == (81 + b) % 113) = true := by
  decide +kernel

/-- Row 81 of the addition table: the network answers (81 + b) % 113 for every b. -/
theorem row_81 : ∀ b, b < 113 → answer 81 b = (81 + b) % 113 := by
  intro b hb
  have h := fast_81 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 81 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 81 b table_ok h.1, h.2]

theorem fast_82 : ∀ b, b < 113 →
    (fastOk E1 E2 448 82 b && fastAnswer E1 E2 W2 448 82 b == (82 + b) % 113) = true := by
  decide +kernel

/-- Row 82 of the addition table: the network answers (82 + b) % 113 for every b. -/
theorem row_82 : ∀ b, b < 113 → answer 82 b = (82 + b) % 113 := by
  intro b hb
  have h := fast_82 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 82 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 82 b table_ok h.1, h.2]

theorem fast_83 : ∀ b, b < 113 →
    (fastOk E1 E2 448 83 b && fastAnswer E1 E2 W2 448 83 b == (83 + b) % 113) = true := by
  decide +kernel

/-- Row 83 of the addition table: the network answers (83 + b) % 113 for every b. -/
theorem row_83 : ∀ b, b < 113 → answer 83 b = (83 + b) % 113 := by
  intro b hb
  have h := fast_83 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 83 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 83 b table_ok h.1, h.2]

theorem fast_84 : ∀ b, b < 113 →
    (fastOk E1 E2 448 84 b && fastAnswer E1 E2 W2 448 84 b == (84 + b) % 113) = true := by
  decide +kernel

/-- Row 84 of the addition table: the network answers (84 + b) % 113 for every b. -/
theorem row_84 : ∀ b, b < 113 → answer 84 b = (84 + b) % 113 := by
  intro b hb
  have h := fast_84 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 84 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 84 b table_ok h.1, h.2]

end LeanCheckedNetwork.FixedPhase448

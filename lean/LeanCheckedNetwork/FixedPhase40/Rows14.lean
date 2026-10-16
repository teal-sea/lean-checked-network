import LeanCheckedNetwork.FixedPhase40.Table

/-! Rows 99 to 105 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.FixedPhase40

open LeanCheckedNetwork

theorem fast_99 : ∀ b, b < 113 →
    (fastOk E1 E2 40 99 b && fastAnswer E1 E2 W2 40 99 b == (99 + b) % 113) = true := by
  decide +kernel

/-- Row 99 of the addition table: the network answers (99 + b) % 113 for every b. -/
theorem row_99 : ∀ b, b < 113 → answer 99 b = (99 + b) % 113 := by
  intro b hb
  have h := fast_99 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 99 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 99 b table_ok h.1, h.2]

theorem fast_100 : ∀ b, b < 113 →
    (fastOk E1 E2 40 100 b && fastAnswer E1 E2 W2 40 100 b == (100 + b) % 113) = true := by
  decide +kernel

/-- Row 100 of the addition table: the network answers (100 + b) % 113 for every b. -/
theorem row_100 : ∀ b, b < 113 → answer 100 b = (100 + b) % 113 := by
  intro b hb
  have h := fast_100 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 100 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 100 b table_ok h.1, h.2]

theorem fast_101 : ∀ b, b < 113 →
    (fastOk E1 E2 40 101 b && fastAnswer E1 E2 W2 40 101 b == (101 + b) % 113) = true := by
  decide +kernel

/-- Row 101 of the addition table: the network answers (101 + b) % 113 for every b. -/
theorem row_101 : ∀ b, b < 113 → answer 101 b = (101 + b) % 113 := by
  intro b hb
  have h := fast_101 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 101 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 101 b table_ok h.1, h.2]

theorem fast_102 : ∀ b, b < 113 →
    (fastOk E1 E2 40 102 b && fastAnswer E1 E2 W2 40 102 b == (102 + b) % 113) = true := by
  decide +kernel

/-- Row 102 of the addition table: the network answers (102 + b) % 113 for every b. -/
theorem row_102 : ∀ b, b < 113 → answer 102 b = (102 + b) % 113 := by
  intro b hb
  have h := fast_102 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 102 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 102 b table_ok h.1, h.2]

theorem fast_103 : ∀ b, b < 113 →
    (fastOk E1 E2 40 103 b && fastAnswer E1 E2 W2 40 103 b == (103 + b) % 113) = true := by
  decide +kernel

/-- Row 103 of the addition table: the network answers (103 + b) % 113 for every b. -/
theorem row_103 : ∀ b, b < 113 → answer 103 b = (103 + b) % 113 := by
  intro b hb
  have h := fast_103 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 103 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 103 b table_ok h.1, h.2]

theorem fast_104 : ∀ b, b < 113 →
    (fastOk E1 E2 40 104 b && fastAnswer E1 E2 W2 40 104 b == (104 + b) % 113) = true := by
  decide +kernel

/-- Row 104 of the addition table: the network answers (104 + b) % 113 for every b. -/
theorem row_104 : ∀ b, b < 113 → answer 104 b = (104 + b) % 113 := by
  intro b hb
  have h := fast_104 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 104 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 104 b table_ok h.1, h.2]

theorem fast_105 : ∀ b, b < 113 →
    (fastOk E1 E2 40 105 b && fastAnswer E1 E2 W2 40 105 b == (105 + b) % 113) = true := by
  decide +kernel

/-- Row 105 of the addition table: the network answers (105 + b) % 113 for every b. -/
theorem row_105 : ∀ b, b < 113 → answer 105 b = (105 + b) % 113 := by
  intro b hb
  have h := fast_105 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 105 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 105 b table_ok h.1, h.2]

end LeanCheckedNetwork.FixedPhase40

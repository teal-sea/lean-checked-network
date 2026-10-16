import LeanCheckedNetwork.FixedPhase16.Table

/-! Rows 29 to 35 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.FixedPhase16

open LeanCheckedNetwork

theorem fast_29 : ∀ b, b < 113 →
    (fastOk E1 E2 16 29 b && fastAnswer E1 E2 W2 16 29 b == (29 + b) % 113) = true := by
  decide +kernel

/-- Row 29 of the addition table: the network answers (29 + b) % 113 for every b. -/
theorem row_29 : ∀ b, b < 113 → answer 29 b = (29 + b) % 113 := by
  intro b hb
  have h := fast_29 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 29 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 16 29 b table_ok h.1, h.2]

theorem fast_30 : ∀ b, b < 113 →
    (fastOk E1 E2 16 30 b && fastAnswer E1 E2 W2 16 30 b == (30 + b) % 113) = true := by
  decide +kernel

/-- Row 30 of the addition table: the network answers (30 + b) % 113 for every b. -/
theorem row_30 : ∀ b, b < 113 → answer 30 b = (30 + b) % 113 := by
  intro b hb
  have h := fast_30 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 30 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 16 30 b table_ok h.1, h.2]

theorem fast_31 : ∀ b, b < 113 →
    (fastOk E1 E2 16 31 b && fastAnswer E1 E2 W2 16 31 b == (31 + b) % 113) = true := by
  decide +kernel

/-- Row 31 of the addition table: the network answers (31 + b) % 113 for every b. -/
theorem row_31 : ∀ b, b < 113 → answer 31 b = (31 + b) % 113 := by
  intro b hb
  have h := fast_31 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 31 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 16 31 b table_ok h.1, h.2]

theorem fast_32 : ∀ b, b < 113 →
    (fastOk E1 E2 16 32 b && fastAnswer E1 E2 W2 16 32 b == (32 + b) % 113) = true := by
  decide +kernel

/-- Row 32 of the addition table: the network answers (32 + b) % 113 for every b. -/
theorem row_32 : ∀ b, b < 113 → answer 32 b = (32 + b) % 113 := by
  intro b hb
  have h := fast_32 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 32 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 16 32 b table_ok h.1, h.2]

theorem fast_33 : ∀ b, b < 113 →
    (fastOk E1 E2 16 33 b && fastAnswer E1 E2 W2 16 33 b == (33 + b) % 113) = true := by
  decide +kernel

/-- Row 33 of the addition table: the network answers (33 + b) % 113 for every b. -/
theorem row_33 : ∀ b, b < 113 → answer 33 b = (33 + b) % 113 := by
  intro b hb
  have h := fast_33 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 33 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 16 33 b table_ok h.1, h.2]

theorem fast_34 : ∀ b, b < 113 →
    (fastOk E1 E2 16 34 b && fastAnswer E1 E2 W2 16 34 b == (34 + b) % 113) = true := by
  decide +kernel

/-- Row 34 of the addition table: the network answers (34 + b) % 113 for every b. -/
theorem row_34 : ∀ b, b < 113 → answer 34 b = (34 + b) % 113 := by
  intro b hb
  have h := fast_34 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 34 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 16 34 b table_ok h.1, h.2]

theorem fast_35 : ∀ b, b < 113 →
    (fastOk E1 E2 16 35 b && fastAnswer E1 E2 W2 16 35 b == (35 + b) % 113) = true := by
  decide +kernel

/-- Row 35 of the addition table: the network answers (35 + b) % 113 for every b. -/
theorem row_35 : ∀ b, b < 113 → answer 35 b = (35 + b) % 113 := by
  intro b hb
  have h := fast_35 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 35 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 16 35 b table_ok h.1, h.2]

end LeanCheckedNetwork.FixedPhase16

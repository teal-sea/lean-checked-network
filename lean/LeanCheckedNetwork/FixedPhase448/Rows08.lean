import LeanCheckedNetwork.FixedPhase448.Table

/-! Rows 57 to 63 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.FixedPhase448

open LeanCheckedNetwork

theorem fast_57 : ∀ b, b < 113 →
    (fastOk E1 E2 448 57 b && fastAnswer E1 E2 W2 448 57 b == (57 + b) % 113) = true := by
  decide +kernel

/-- Row 57 of the addition table: the network answers (57 + b) % 113 for every b. -/
theorem row_57 : ∀ b, b < 113 → answer 57 b = (57 + b) % 113 := by
  intro b hb
  have h := fast_57 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 57 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 57 b table_ok h.1, h.2]

theorem fast_58 : ∀ b, b < 113 →
    (fastOk E1 E2 448 58 b && fastAnswer E1 E2 W2 448 58 b == (58 + b) % 113) = true := by
  decide +kernel

/-- Row 58 of the addition table: the network answers (58 + b) % 113 for every b. -/
theorem row_58 : ∀ b, b < 113 → answer 58 b = (58 + b) % 113 := by
  intro b hb
  have h := fast_58 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 58 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 58 b table_ok h.1, h.2]

theorem fast_59 : ∀ b, b < 113 →
    (fastOk E1 E2 448 59 b && fastAnswer E1 E2 W2 448 59 b == (59 + b) % 113) = true := by
  decide +kernel

/-- Row 59 of the addition table: the network answers (59 + b) % 113 for every b. -/
theorem row_59 : ∀ b, b < 113 → answer 59 b = (59 + b) % 113 := by
  intro b hb
  have h := fast_59 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 59 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 59 b table_ok h.1, h.2]

theorem fast_60 : ∀ b, b < 113 →
    (fastOk E1 E2 448 60 b && fastAnswer E1 E2 W2 448 60 b == (60 + b) % 113) = true := by
  decide +kernel

/-- Row 60 of the addition table: the network answers (60 + b) % 113 for every b. -/
theorem row_60 : ∀ b, b < 113 → answer 60 b = (60 + b) % 113 := by
  intro b hb
  have h := fast_60 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 60 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 60 b table_ok h.1, h.2]

theorem fast_61 : ∀ b, b < 113 →
    (fastOk E1 E2 448 61 b && fastAnswer E1 E2 W2 448 61 b == (61 + b) % 113) = true := by
  decide +kernel

/-- Row 61 of the addition table: the network answers (61 + b) % 113 for every b. -/
theorem row_61 : ∀ b, b < 113 → answer 61 b = (61 + b) % 113 := by
  intro b hb
  have h := fast_61 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 61 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 61 b table_ok h.1, h.2]

theorem fast_62 : ∀ b, b < 113 →
    (fastOk E1 E2 448 62 b && fastAnswer E1 E2 W2 448 62 b == (62 + b) % 113) = true := by
  decide +kernel

/-- Row 62 of the addition table: the network answers (62 + b) % 113 for every b. -/
theorem row_62 : ∀ b, b < 113 → answer 62 b = (62 + b) % 113 := by
  intro b hb
  have h := fast_62 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 62 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 62 b table_ok h.1, h.2]

theorem fast_63 : ∀ b, b < 113 →
    (fastOk E1 E2 448 63 b && fastAnswer E1 E2 W2 448 63 b == (63 + b) % 113) = true := by
  decide +kernel

/-- Row 63 of the addition table: the network answers (63 + b) % 113 for every b. -/
theorem row_63 : ∀ b, b < 113 → answer 63 b = (63 + b) % 113 := by
  intro b hb
  have h := fast_63 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 63 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 63 b table_ok h.1, h.2]

end LeanCheckedNetwork.FixedPhase448

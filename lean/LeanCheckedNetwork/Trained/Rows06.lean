import LeanCheckedNetwork.Trained.Table

/-! Rows 43 to 49 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Trained

open LeanCheckedNetwork

theorem fast_43 : ∀ b, b < 113 →
    (fastOk E1 E2 128 43 b && fastAnswer E1 E2 W2 128 43 b == (43 + b) % 113) = true := by
  decide +kernel

/-- Row 43 of the addition table: the network answers (43 + b) % 113 for every b. -/
theorem row_43 : ∀ b, b < 113 → answer 43 b = (43 + b) % 113 := by
  intro b hb
  have h := fast_43 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 43 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 43 b table_ok h.1, h.2]

theorem fast_44 : ∀ b, b < 113 →
    (fastOk E1 E2 128 44 b && fastAnswer E1 E2 W2 128 44 b == (44 + b) % 113) = true := by
  decide +kernel

/-- Row 44 of the addition table: the network answers (44 + b) % 113 for every b. -/
theorem row_44 : ∀ b, b < 113 → answer 44 b = (44 + b) % 113 := by
  intro b hb
  have h := fast_44 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 44 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 44 b table_ok h.1, h.2]

theorem fast_45 : ∀ b, b < 113 →
    (fastOk E1 E2 128 45 b && fastAnswer E1 E2 W2 128 45 b == (45 + b) % 113) = true := by
  decide +kernel

/-- Row 45 of the addition table: the network answers (45 + b) % 113 for every b. -/
theorem row_45 : ∀ b, b < 113 → answer 45 b = (45 + b) % 113 := by
  intro b hb
  have h := fast_45 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 45 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 45 b table_ok h.1, h.2]

theorem fast_46 : ∀ b, b < 113 →
    (fastOk E1 E2 128 46 b && fastAnswer E1 E2 W2 128 46 b == (46 + b) % 113) = true := by
  decide +kernel

/-- Row 46 of the addition table: the network answers (46 + b) % 113 for every b. -/
theorem row_46 : ∀ b, b < 113 → answer 46 b = (46 + b) % 113 := by
  intro b hb
  have h := fast_46 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 46 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 46 b table_ok h.1, h.2]

theorem fast_47 : ∀ b, b < 113 →
    (fastOk E1 E2 128 47 b && fastAnswer E1 E2 W2 128 47 b == (47 + b) % 113) = true := by
  decide +kernel

/-- Row 47 of the addition table: the network answers (47 + b) % 113 for every b. -/
theorem row_47 : ∀ b, b < 113 → answer 47 b = (47 + b) % 113 := by
  intro b hb
  have h := fast_47 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 47 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 47 b table_ok h.1, h.2]

theorem fast_48 : ∀ b, b < 113 →
    (fastOk E1 E2 128 48 b && fastAnswer E1 E2 W2 128 48 b == (48 + b) % 113) = true := by
  decide +kernel

/-- Row 48 of the addition table: the network answers (48 + b) % 113 for every b. -/
theorem row_48 : ∀ b, b < 113 → answer 48 b = (48 + b) % 113 := by
  intro b hb
  have h := fast_48 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 48 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 48 b table_ok h.1, h.2]

theorem fast_49 : ∀ b, b < 113 →
    (fastOk E1 E2 128 49 b && fastAnswer E1 E2 W2 128 49 b == (49 + b) % 113) = true := by
  decide +kernel

/-- Row 49 of the addition table: the network answers (49 + b) % 113 for every b. -/
theorem row_49 : ∀ b, b < 113 → answer 49 b = (49 + b) % 113 := by
  intro b hb
  have h := fast_49 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 49 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 49 b table_ok h.1, h.2]

end LeanCheckedNetwork.Trained

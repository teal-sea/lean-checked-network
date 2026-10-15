import LeanCheckedNetwork.Trained.Table

/-! Rows 15 to 21 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Trained

open LeanCheckedNetwork

theorem fast_15 : ∀ b, b < 113 →
    (fastOk E1 E2 128 15 b && fastAnswer E1 E2 W2 128 15 b == (15 + b) % 113) = true := by
  decide +kernel

/-- Row 15 of the addition table: the network answers (15 + b) % 113 for every b. -/
theorem row_15 : ∀ b, b < 113 → answer 15 b = (15 + b) % 113 := by
  intro b hb
  have h := fast_15 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 15 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 15 b table_ok h.1, h.2]

theorem fast_16 : ∀ b, b < 113 →
    (fastOk E1 E2 128 16 b && fastAnswer E1 E2 W2 128 16 b == (16 + b) % 113) = true := by
  decide +kernel

/-- Row 16 of the addition table: the network answers (16 + b) % 113 for every b. -/
theorem row_16 : ∀ b, b < 113 → answer 16 b = (16 + b) % 113 := by
  intro b hb
  have h := fast_16 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 16 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 16 b table_ok h.1, h.2]

theorem fast_17 : ∀ b, b < 113 →
    (fastOk E1 E2 128 17 b && fastAnswer E1 E2 W2 128 17 b == (17 + b) % 113) = true := by
  decide +kernel

/-- Row 17 of the addition table: the network answers (17 + b) % 113 for every b. -/
theorem row_17 : ∀ b, b < 113 → answer 17 b = (17 + b) % 113 := by
  intro b hb
  have h := fast_17 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 17 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 17 b table_ok h.1, h.2]

theorem fast_18 : ∀ b, b < 113 →
    (fastOk E1 E2 128 18 b && fastAnswer E1 E2 W2 128 18 b == (18 + b) % 113) = true := by
  decide +kernel

/-- Row 18 of the addition table: the network answers (18 + b) % 113 for every b. -/
theorem row_18 : ∀ b, b < 113 → answer 18 b = (18 + b) % 113 := by
  intro b hb
  have h := fast_18 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 18 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 18 b table_ok h.1, h.2]

theorem fast_19 : ∀ b, b < 113 →
    (fastOk E1 E2 128 19 b && fastAnswer E1 E2 W2 128 19 b == (19 + b) % 113) = true := by
  decide +kernel

/-- Row 19 of the addition table: the network answers (19 + b) % 113 for every b. -/
theorem row_19 : ∀ b, b < 113 → answer 19 b = (19 + b) % 113 := by
  intro b hb
  have h := fast_19 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 19 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 19 b table_ok h.1, h.2]

theorem fast_20 : ∀ b, b < 113 →
    (fastOk E1 E2 128 20 b && fastAnswer E1 E2 W2 128 20 b == (20 + b) % 113) = true := by
  decide +kernel

/-- Row 20 of the addition table: the network answers (20 + b) % 113 for every b. -/
theorem row_20 : ∀ b, b < 113 → answer 20 b = (20 + b) % 113 := by
  intro b hb
  have h := fast_20 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 20 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 20 b table_ok h.1, h.2]

theorem fast_21 : ∀ b, b < 113 →
    (fastOk E1 E2 128 21 b && fastAnswer E1 E2 W2 128 21 b == (21 + b) % 113) = true := by
  decide +kernel

/-- Row 21 of the addition table: the network answers (21 + b) % 113 for every b. -/
theorem row_21 : ∀ b, b < 113 → answer 21 b = (21 + b) % 113 := by
  intro b hb
  have h := fast_21 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 21 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 128 21 b table_ok h.1, h.2]

end LeanCheckedNetwork.Trained

import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 25 to 32 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_25 : ∀ b, b < 257 →
    (fastOk E1 E2 12 25 b && fastAnswer E1 E2 W2 12 25 b == (25 + b) % 257) = true := by
  decide +kernel

/-- Row 25 of the addition table: the network answers (25 + b) % 257 for every b. -/
theorem row_25 : ∀ b, b < 257 → answer 25 b = (25 + b) % 257 := by
  intro b hb
  have h := fast_25 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 25 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 25 b table_ok h.1, h.2]

theorem fast_26 : ∀ b, b < 257 →
    (fastOk E1 E2 12 26 b && fastAnswer E1 E2 W2 12 26 b == (26 + b) % 257) = true := by
  decide +kernel

/-- Row 26 of the addition table: the network answers (26 + b) % 257 for every b. -/
theorem row_26 : ∀ b, b < 257 → answer 26 b = (26 + b) % 257 := by
  intro b hb
  have h := fast_26 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 26 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 26 b table_ok h.1, h.2]

theorem fast_27 : ∀ b, b < 257 →
    (fastOk E1 E2 12 27 b && fastAnswer E1 E2 W2 12 27 b == (27 + b) % 257) = true := by
  decide +kernel

/-- Row 27 of the addition table: the network answers (27 + b) % 257 for every b. -/
theorem row_27 : ∀ b, b < 257 → answer 27 b = (27 + b) % 257 := by
  intro b hb
  have h := fast_27 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 27 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 27 b table_ok h.1, h.2]

theorem fast_28 : ∀ b, b < 257 →
    (fastOk E1 E2 12 28 b && fastAnswer E1 E2 W2 12 28 b == (28 + b) % 257) = true := by
  decide +kernel

/-- Row 28 of the addition table: the network answers (28 + b) % 257 for every b. -/
theorem row_28 : ∀ b, b < 257 → answer 28 b = (28 + b) % 257 := by
  intro b hb
  have h := fast_28 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 28 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 28 b table_ok h.1, h.2]

theorem fast_29 : ∀ b, b < 257 →
    (fastOk E1 E2 12 29 b && fastAnswer E1 E2 W2 12 29 b == (29 + b) % 257) = true := by
  decide +kernel

/-- Row 29 of the addition table: the network answers (29 + b) % 257 for every b. -/
theorem row_29 : ∀ b, b < 257 → answer 29 b = (29 + b) % 257 := by
  intro b hb
  have h := fast_29 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 29 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 29 b table_ok h.1, h.2]

theorem fast_30 : ∀ b, b < 257 →
    (fastOk E1 E2 12 30 b && fastAnswer E1 E2 W2 12 30 b == (30 + b) % 257) = true := by
  decide +kernel

/-- Row 30 of the addition table: the network answers (30 + b) % 257 for every b. -/
theorem row_30 : ∀ b, b < 257 → answer 30 b = (30 + b) % 257 := by
  intro b hb
  have h := fast_30 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 30 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 30 b table_ok h.1, h.2]

theorem fast_31 : ∀ b, b < 257 →
    (fastOk E1 E2 12 31 b && fastAnswer E1 E2 W2 12 31 b == (31 + b) % 257) = true := by
  decide +kernel

/-- Row 31 of the addition table: the network answers (31 + b) % 257 for every b. -/
theorem row_31 : ∀ b, b < 257 → answer 31 b = (31 + b) % 257 := by
  intro b hb
  have h := fast_31 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 31 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 31 b table_ok h.1, h.2]

theorem fast_32 : ∀ b, b < 257 →
    (fastOk E1 E2 12 32 b && fastAnswer E1 E2 W2 12 32 b == (32 + b) % 257) = true := by
  decide +kernel

/-- Row 32 of the addition table: the network answers (32 + b) % 257 for every b. -/
theorem row_32 : ∀ b, b < 257 → answer 32 b = (32 + b) % 257 := by
  intro b hb
  have h := fast_32 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 32 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 32 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

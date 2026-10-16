import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 9 to 16 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_9 : ∀ b, b < 257 →
    (fastOk E1 E2 12 9 b && fastAnswer E1 E2 W2 12 9 b == (9 + b) % 257) = true := by
  decide +kernel

/-- Row 9 of the addition table: the network answers (9 + b) % 257 for every b. -/
theorem row_9 : ∀ b, b < 257 → answer 9 b = (9 + b) % 257 := by
  intro b hb
  have h := fast_9 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 9 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 9 b table_ok h.1, h.2]

theorem fast_10 : ∀ b, b < 257 →
    (fastOk E1 E2 12 10 b && fastAnswer E1 E2 W2 12 10 b == (10 + b) % 257) = true := by
  decide +kernel

/-- Row 10 of the addition table: the network answers (10 + b) % 257 for every b. -/
theorem row_10 : ∀ b, b < 257 → answer 10 b = (10 + b) % 257 := by
  intro b hb
  have h := fast_10 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 10 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 10 b table_ok h.1, h.2]

theorem fast_11 : ∀ b, b < 257 →
    (fastOk E1 E2 12 11 b && fastAnswer E1 E2 W2 12 11 b == (11 + b) % 257) = true := by
  decide +kernel

/-- Row 11 of the addition table: the network answers (11 + b) % 257 for every b. -/
theorem row_11 : ∀ b, b < 257 → answer 11 b = (11 + b) % 257 := by
  intro b hb
  have h := fast_11 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 11 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 11 b table_ok h.1, h.2]

theorem fast_12 : ∀ b, b < 257 →
    (fastOk E1 E2 12 12 b && fastAnswer E1 E2 W2 12 12 b == (12 + b) % 257) = true := by
  decide +kernel

/-- Row 12 of the addition table: the network answers (12 + b) % 257 for every b. -/
theorem row_12 : ∀ b, b < 257 → answer 12 b = (12 + b) % 257 := by
  intro b hb
  have h := fast_12 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 12 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 12 b table_ok h.1, h.2]

theorem fast_13 : ∀ b, b < 257 →
    (fastOk E1 E2 12 13 b && fastAnswer E1 E2 W2 12 13 b == (13 + b) % 257) = true := by
  decide +kernel

/-- Row 13 of the addition table: the network answers (13 + b) % 257 for every b. -/
theorem row_13 : ∀ b, b < 257 → answer 13 b = (13 + b) % 257 := by
  intro b hb
  have h := fast_13 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 13 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 13 b table_ok h.1, h.2]

theorem fast_14 : ∀ b, b < 257 →
    (fastOk E1 E2 12 14 b && fastAnswer E1 E2 W2 12 14 b == (14 + b) % 257) = true := by
  decide +kernel

/-- Row 14 of the addition table: the network answers (14 + b) % 257 for every b. -/
theorem row_14 : ∀ b, b < 257 → answer 14 b = (14 + b) % 257 := by
  intro b hb
  have h := fast_14 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 14 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 14 b table_ok h.1, h.2]

theorem fast_15 : ∀ b, b < 257 →
    (fastOk E1 E2 12 15 b && fastAnswer E1 E2 W2 12 15 b == (15 + b) % 257) = true := by
  decide +kernel

/-- Row 15 of the addition table: the network answers (15 + b) % 257 for every b. -/
theorem row_15 : ∀ b, b < 257 → answer 15 b = (15 + b) % 257 := by
  intro b hb
  have h := fast_15 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 15 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 15 b table_ok h.1, h.2]

theorem fast_16 : ∀ b, b < 257 →
    (fastOk E1 E2 12 16 b && fastAnswer E1 E2 W2 12 16 b == (16 + b) % 257) = true := by
  decide +kernel

/-- Row 16 of the addition table: the network answers (16 + b) % 257 for every b. -/
theorem row_16 : ∀ b, b < 257 → answer 16 b = (16 + b) % 257 := by
  intro b hb
  have h := fast_16 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 16 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 16 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

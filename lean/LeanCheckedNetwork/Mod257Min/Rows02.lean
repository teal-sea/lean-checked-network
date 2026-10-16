import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 17 to 24 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_17 : ∀ b, b < 257 →
    (fastOk E1 E2 12 17 b && fastAnswer E1 E2 W2 12 17 b == (17 + b) % 257) = true := by
  decide +kernel

/-- Row 17 of the addition table: the network answers (17 + b) % 257 for every b. -/
theorem row_17 : ∀ b, b < 257 → answer 17 b = (17 + b) % 257 := by
  intro b hb
  have h := fast_17 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 17 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 17 b table_ok h.1, h.2]

theorem fast_18 : ∀ b, b < 257 →
    (fastOk E1 E2 12 18 b && fastAnswer E1 E2 W2 12 18 b == (18 + b) % 257) = true := by
  decide +kernel

/-- Row 18 of the addition table: the network answers (18 + b) % 257 for every b. -/
theorem row_18 : ∀ b, b < 257 → answer 18 b = (18 + b) % 257 := by
  intro b hb
  have h := fast_18 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 18 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 18 b table_ok h.1, h.2]

theorem fast_19 : ∀ b, b < 257 →
    (fastOk E1 E2 12 19 b && fastAnswer E1 E2 W2 12 19 b == (19 + b) % 257) = true := by
  decide +kernel

/-- Row 19 of the addition table: the network answers (19 + b) % 257 for every b. -/
theorem row_19 : ∀ b, b < 257 → answer 19 b = (19 + b) % 257 := by
  intro b hb
  have h := fast_19 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 19 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 19 b table_ok h.1, h.2]

theorem fast_20 : ∀ b, b < 257 →
    (fastOk E1 E2 12 20 b && fastAnswer E1 E2 W2 12 20 b == (20 + b) % 257) = true := by
  decide +kernel

/-- Row 20 of the addition table: the network answers (20 + b) % 257 for every b. -/
theorem row_20 : ∀ b, b < 257 → answer 20 b = (20 + b) % 257 := by
  intro b hb
  have h := fast_20 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 20 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 20 b table_ok h.1, h.2]

theorem fast_21 : ∀ b, b < 257 →
    (fastOk E1 E2 12 21 b && fastAnswer E1 E2 W2 12 21 b == (21 + b) % 257) = true := by
  decide +kernel

/-- Row 21 of the addition table: the network answers (21 + b) % 257 for every b. -/
theorem row_21 : ∀ b, b < 257 → answer 21 b = (21 + b) % 257 := by
  intro b hb
  have h := fast_21 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 21 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 21 b table_ok h.1, h.2]

theorem fast_22 : ∀ b, b < 257 →
    (fastOk E1 E2 12 22 b && fastAnswer E1 E2 W2 12 22 b == (22 + b) % 257) = true := by
  decide +kernel

/-- Row 22 of the addition table: the network answers (22 + b) % 257 for every b. -/
theorem row_22 : ∀ b, b < 257 → answer 22 b = (22 + b) % 257 := by
  intro b hb
  have h := fast_22 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 22 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 22 b table_ok h.1, h.2]

theorem fast_23 : ∀ b, b < 257 →
    (fastOk E1 E2 12 23 b && fastAnswer E1 E2 W2 12 23 b == (23 + b) % 257) = true := by
  decide +kernel

/-- Row 23 of the addition table: the network answers (23 + b) % 257 for every b. -/
theorem row_23 : ∀ b, b < 257 → answer 23 b = (23 + b) % 257 := by
  intro b hb
  have h := fast_23 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 23 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 23 b table_ok h.1, h.2]

theorem fast_24 : ∀ b, b < 257 →
    (fastOk E1 E2 12 24 b && fastAnswer E1 E2 W2 12 24 b == (24 + b) % 257) = true := by
  decide +kernel

/-- Row 24 of the addition table: the network answers (24 + b) % 257 for every b. -/
theorem row_24 : ∀ b, b < 257 → answer 24 b = (24 + b) % 257 := by
  intro b hb
  have h := fast_24 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 24 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 24 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

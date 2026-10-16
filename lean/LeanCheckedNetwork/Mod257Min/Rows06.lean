import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 49 to 56 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_49 : ∀ b, b < 257 →
    (fastOk E1 E2 12 49 b && fastAnswer E1 E2 W2 12 49 b == (49 + b) % 257) = true := by
  decide +kernel

/-- Row 49 of the addition table: the network answers (49 + b) % 257 for every b. -/
theorem row_49 : ∀ b, b < 257 → answer 49 b = (49 + b) % 257 := by
  intro b hb
  have h := fast_49 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 49 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 49 b table_ok h.1, h.2]

theorem fast_50 : ∀ b, b < 257 →
    (fastOk E1 E2 12 50 b && fastAnswer E1 E2 W2 12 50 b == (50 + b) % 257) = true := by
  decide +kernel

/-- Row 50 of the addition table: the network answers (50 + b) % 257 for every b. -/
theorem row_50 : ∀ b, b < 257 → answer 50 b = (50 + b) % 257 := by
  intro b hb
  have h := fast_50 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 50 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 50 b table_ok h.1, h.2]

theorem fast_51 : ∀ b, b < 257 →
    (fastOk E1 E2 12 51 b && fastAnswer E1 E2 W2 12 51 b == (51 + b) % 257) = true := by
  decide +kernel

/-- Row 51 of the addition table: the network answers (51 + b) % 257 for every b. -/
theorem row_51 : ∀ b, b < 257 → answer 51 b = (51 + b) % 257 := by
  intro b hb
  have h := fast_51 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 51 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 51 b table_ok h.1, h.2]

theorem fast_52 : ∀ b, b < 257 →
    (fastOk E1 E2 12 52 b && fastAnswer E1 E2 W2 12 52 b == (52 + b) % 257) = true := by
  decide +kernel

/-- Row 52 of the addition table: the network answers (52 + b) % 257 for every b. -/
theorem row_52 : ∀ b, b < 257 → answer 52 b = (52 + b) % 257 := by
  intro b hb
  have h := fast_52 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 52 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 52 b table_ok h.1, h.2]

theorem fast_53 : ∀ b, b < 257 →
    (fastOk E1 E2 12 53 b && fastAnswer E1 E2 W2 12 53 b == (53 + b) % 257) = true := by
  decide +kernel

/-- Row 53 of the addition table: the network answers (53 + b) % 257 for every b. -/
theorem row_53 : ∀ b, b < 257 → answer 53 b = (53 + b) % 257 := by
  intro b hb
  have h := fast_53 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 53 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 53 b table_ok h.1, h.2]

theorem fast_54 : ∀ b, b < 257 →
    (fastOk E1 E2 12 54 b && fastAnswer E1 E2 W2 12 54 b == (54 + b) % 257) = true := by
  decide +kernel

/-- Row 54 of the addition table: the network answers (54 + b) % 257 for every b. -/
theorem row_54 : ∀ b, b < 257 → answer 54 b = (54 + b) % 257 := by
  intro b hb
  have h := fast_54 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 54 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 54 b table_ok h.1, h.2]

theorem fast_55 : ∀ b, b < 257 →
    (fastOk E1 E2 12 55 b && fastAnswer E1 E2 W2 12 55 b == (55 + b) % 257) = true := by
  decide +kernel

/-- Row 55 of the addition table: the network answers (55 + b) % 257 for every b. -/
theorem row_55 : ∀ b, b < 257 → answer 55 b = (55 + b) % 257 := by
  intro b hb
  have h := fast_55 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 55 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 55 b table_ok h.1, h.2]

theorem fast_56 : ∀ b, b < 257 →
    (fastOk E1 E2 12 56 b && fastAnswer E1 E2 W2 12 56 b == (56 + b) % 257) = true := by
  decide +kernel

/-- Row 56 of the addition table: the network answers (56 + b) % 257 for every b. -/
theorem row_56 : ∀ b, b < 257 → answer 56 b = (56 + b) % 257 := by
  intro b hb
  have h := fast_56 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 56 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 56 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

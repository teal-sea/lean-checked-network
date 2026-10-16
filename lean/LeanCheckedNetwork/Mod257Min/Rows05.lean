import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 41 to 48 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_41 : ∀ b, b < 257 →
    (fastOk E1 E2 12 41 b && fastAnswer E1 E2 W2 12 41 b == (41 + b) % 257) = true := by
  decide +kernel

/-- Row 41 of the addition table: the network answers (41 + b) % 257 for every b. -/
theorem row_41 : ∀ b, b < 257 → answer 41 b = (41 + b) % 257 := by
  intro b hb
  have h := fast_41 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 41 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 41 b table_ok h.1, h.2]

theorem fast_42 : ∀ b, b < 257 →
    (fastOk E1 E2 12 42 b && fastAnswer E1 E2 W2 12 42 b == (42 + b) % 257) = true := by
  decide +kernel

/-- Row 42 of the addition table: the network answers (42 + b) % 257 for every b. -/
theorem row_42 : ∀ b, b < 257 → answer 42 b = (42 + b) % 257 := by
  intro b hb
  have h := fast_42 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 42 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 42 b table_ok h.1, h.2]

theorem fast_43 : ∀ b, b < 257 →
    (fastOk E1 E2 12 43 b && fastAnswer E1 E2 W2 12 43 b == (43 + b) % 257) = true := by
  decide +kernel

/-- Row 43 of the addition table: the network answers (43 + b) % 257 for every b. -/
theorem row_43 : ∀ b, b < 257 → answer 43 b = (43 + b) % 257 := by
  intro b hb
  have h := fast_43 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 43 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 43 b table_ok h.1, h.2]

theorem fast_44 : ∀ b, b < 257 →
    (fastOk E1 E2 12 44 b && fastAnswer E1 E2 W2 12 44 b == (44 + b) % 257) = true := by
  decide +kernel

/-- Row 44 of the addition table: the network answers (44 + b) % 257 for every b. -/
theorem row_44 : ∀ b, b < 257 → answer 44 b = (44 + b) % 257 := by
  intro b hb
  have h := fast_44 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 44 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 44 b table_ok h.1, h.2]

theorem fast_45 : ∀ b, b < 257 →
    (fastOk E1 E2 12 45 b && fastAnswer E1 E2 W2 12 45 b == (45 + b) % 257) = true := by
  decide +kernel

/-- Row 45 of the addition table: the network answers (45 + b) % 257 for every b. -/
theorem row_45 : ∀ b, b < 257 → answer 45 b = (45 + b) % 257 := by
  intro b hb
  have h := fast_45 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 45 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 45 b table_ok h.1, h.2]

theorem fast_46 : ∀ b, b < 257 →
    (fastOk E1 E2 12 46 b && fastAnswer E1 E2 W2 12 46 b == (46 + b) % 257) = true := by
  decide +kernel

/-- Row 46 of the addition table: the network answers (46 + b) % 257 for every b. -/
theorem row_46 : ∀ b, b < 257 → answer 46 b = (46 + b) % 257 := by
  intro b hb
  have h := fast_46 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 46 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 46 b table_ok h.1, h.2]

theorem fast_47 : ∀ b, b < 257 →
    (fastOk E1 E2 12 47 b && fastAnswer E1 E2 W2 12 47 b == (47 + b) % 257) = true := by
  decide +kernel

/-- Row 47 of the addition table: the network answers (47 + b) % 257 for every b. -/
theorem row_47 : ∀ b, b < 257 → answer 47 b = (47 + b) % 257 := by
  intro b hb
  have h := fast_47 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 47 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 47 b table_ok h.1, h.2]

theorem fast_48 : ∀ b, b < 257 →
    (fastOk E1 E2 12 48 b && fastAnswer E1 E2 W2 12 48 b == (48 + b) % 257) = true := by
  decide +kernel

/-- Row 48 of the addition table: the network answers (48 + b) % 257 for every b. -/
theorem row_48 : ∀ b, b < 257 → answer 48 b = (48 + b) % 257 := by
  intro b hb
  have h := fast_48 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 48 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 48 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

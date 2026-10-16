import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 65 to 72 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_65 : ∀ b, b < 257 →
    (fastOk E1 E2 12 65 b && fastAnswer E1 E2 W2 12 65 b == (65 + b) % 257) = true := by
  decide +kernel

/-- Row 65 of the addition table: the network answers (65 + b) % 257 for every b. -/
theorem row_65 : ∀ b, b < 257 → answer 65 b = (65 + b) % 257 := by
  intro b hb
  have h := fast_65 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 65 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 65 b table_ok h.1, h.2]

theorem fast_66 : ∀ b, b < 257 →
    (fastOk E1 E2 12 66 b && fastAnswer E1 E2 W2 12 66 b == (66 + b) % 257) = true := by
  decide +kernel

/-- Row 66 of the addition table: the network answers (66 + b) % 257 for every b. -/
theorem row_66 : ∀ b, b < 257 → answer 66 b = (66 + b) % 257 := by
  intro b hb
  have h := fast_66 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 66 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 66 b table_ok h.1, h.2]

theorem fast_67 : ∀ b, b < 257 →
    (fastOk E1 E2 12 67 b && fastAnswer E1 E2 W2 12 67 b == (67 + b) % 257) = true := by
  decide +kernel

/-- Row 67 of the addition table: the network answers (67 + b) % 257 for every b. -/
theorem row_67 : ∀ b, b < 257 → answer 67 b = (67 + b) % 257 := by
  intro b hb
  have h := fast_67 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 67 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 67 b table_ok h.1, h.2]

theorem fast_68 : ∀ b, b < 257 →
    (fastOk E1 E2 12 68 b && fastAnswer E1 E2 W2 12 68 b == (68 + b) % 257) = true := by
  decide +kernel

/-- Row 68 of the addition table: the network answers (68 + b) % 257 for every b. -/
theorem row_68 : ∀ b, b < 257 → answer 68 b = (68 + b) % 257 := by
  intro b hb
  have h := fast_68 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 68 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 68 b table_ok h.1, h.2]

theorem fast_69 : ∀ b, b < 257 →
    (fastOk E1 E2 12 69 b && fastAnswer E1 E2 W2 12 69 b == (69 + b) % 257) = true := by
  decide +kernel

/-- Row 69 of the addition table: the network answers (69 + b) % 257 for every b. -/
theorem row_69 : ∀ b, b < 257 → answer 69 b = (69 + b) % 257 := by
  intro b hb
  have h := fast_69 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 69 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 69 b table_ok h.1, h.2]

theorem fast_70 : ∀ b, b < 257 →
    (fastOk E1 E2 12 70 b && fastAnswer E1 E2 W2 12 70 b == (70 + b) % 257) = true := by
  decide +kernel

/-- Row 70 of the addition table: the network answers (70 + b) % 257 for every b. -/
theorem row_70 : ∀ b, b < 257 → answer 70 b = (70 + b) % 257 := by
  intro b hb
  have h := fast_70 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 70 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 70 b table_ok h.1, h.2]

theorem fast_71 : ∀ b, b < 257 →
    (fastOk E1 E2 12 71 b && fastAnswer E1 E2 W2 12 71 b == (71 + b) % 257) = true := by
  decide +kernel

/-- Row 71 of the addition table: the network answers (71 + b) % 257 for every b. -/
theorem row_71 : ∀ b, b < 257 → answer 71 b = (71 + b) % 257 := by
  intro b hb
  have h := fast_71 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 71 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 71 b table_ok h.1, h.2]

theorem fast_72 : ∀ b, b < 257 →
    (fastOk E1 E2 12 72 b && fastAnswer E1 E2 W2 12 72 b == (72 + b) % 257) = true := by
  decide +kernel

/-- Row 72 of the addition table: the network answers (72 + b) % 257 for every b. -/
theorem row_72 : ∀ b, b < 257 → answer 72 b = (72 + b) % 257 := by
  intro b hb
  have h := fast_72 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 72 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 72 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

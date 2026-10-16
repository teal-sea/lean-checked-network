import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 121 to 128 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_121 : ∀ b, b < 257 →
    (fastOk E1 E2 12 121 b && fastAnswer E1 E2 W2 12 121 b == (121 + b) % 257) = true := by
  decide +kernel

/-- Row 121 of the addition table: the network answers (121 + b) % 257 for every b. -/
theorem row_121 : ∀ b, b < 257 → answer 121 b = (121 + b) % 257 := by
  intro b hb
  have h := fast_121 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 121 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 121 b table_ok h.1, h.2]

theorem fast_122 : ∀ b, b < 257 →
    (fastOk E1 E2 12 122 b && fastAnswer E1 E2 W2 12 122 b == (122 + b) % 257) = true := by
  decide +kernel

/-- Row 122 of the addition table: the network answers (122 + b) % 257 for every b. -/
theorem row_122 : ∀ b, b < 257 → answer 122 b = (122 + b) % 257 := by
  intro b hb
  have h := fast_122 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 122 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 122 b table_ok h.1, h.2]

theorem fast_123 : ∀ b, b < 257 →
    (fastOk E1 E2 12 123 b && fastAnswer E1 E2 W2 12 123 b == (123 + b) % 257) = true := by
  decide +kernel

/-- Row 123 of the addition table: the network answers (123 + b) % 257 for every b. -/
theorem row_123 : ∀ b, b < 257 → answer 123 b = (123 + b) % 257 := by
  intro b hb
  have h := fast_123 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 123 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 123 b table_ok h.1, h.2]

theorem fast_124 : ∀ b, b < 257 →
    (fastOk E1 E2 12 124 b && fastAnswer E1 E2 W2 12 124 b == (124 + b) % 257) = true := by
  decide +kernel

/-- Row 124 of the addition table: the network answers (124 + b) % 257 for every b. -/
theorem row_124 : ∀ b, b < 257 → answer 124 b = (124 + b) % 257 := by
  intro b hb
  have h := fast_124 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 124 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 124 b table_ok h.1, h.2]

theorem fast_125 : ∀ b, b < 257 →
    (fastOk E1 E2 12 125 b && fastAnswer E1 E2 W2 12 125 b == (125 + b) % 257) = true := by
  decide +kernel

/-- Row 125 of the addition table: the network answers (125 + b) % 257 for every b. -/
theorem row_125 : ∀ b, b < 257 → answer 125 b = (125 + b) % 257 := by
  intro b hb
  have h := fast_125 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 125 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 125 b table_ok h.1, h.2]

theorem fast_126 : ∀ b, b < 257 →
    (fastOk E1 E2 12 126 b && fastAnswer E1 E2 W2 12 126 b == (126 + b) % 257) = true := by
  decide +kernel

/-- Row 126 of the addition table: the network answers (126 + b) % 257 for every b. -/
theorem row_126 : ∀ b, b < 257 → answer 126 b = (126 + b) % 257 := by
  intro b hb
  have h := fast_126 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 126 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 126 b table_ok h.1, h.2]

theorem fast_127 : ∀ b, b < 257 →
    (fastOk E1 E2 12 127 b && fastAnswer E1 E2 W2 12 127 b == (127 + b) % 257) = true := by
  decide +kernel

/-- Row 127 of the addition table: the network answers (127 + b) % 257 for every b. -/
theorem row_127 : ∀ b, b < 257 → answer 127 b = (127 + b) % 257 := by
  intro b hb
  have h := fast_127 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 127 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 127 b table_ok h.1, h.2]

theorem fast_128 : ∀ b, b < 257 →
    (fastOk E1 E2 12 128 b && fastAnswer E1 E2 W2 12 128 b == (128 + b) % 257) = true := by
  decide +kernel

/-- Row 128 of the addition table: the network answers (128 + b) % 257 for every b. -/
theorem row_128 : ∀ b, b < 257 → answer 128 b = (128 + b) % 257 := by
  intro b hb
  have h := fast_128 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 128 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 128 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

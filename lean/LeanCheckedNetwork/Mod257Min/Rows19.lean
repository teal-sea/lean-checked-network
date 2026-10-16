import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 153 to 160 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_153 : ∀ b, b < 257 →
    (fastOk E1 E2 12 153 b && fastAnswer E1 E2 W2 12 153 b == (153 + b) % 257) = true := by
  decide +kernel

/-- Row 153 of the addition table: the network answers (153 + b) % 257 for every b. -/
theorem row_153 : ∀ b, b < 257 → answer 153 b = (153 + b) % 257 := by
  intro b hb
  have h := fast_153 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 153 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 153 b table_ok h.1, h.2]

theorem fast_154 : ∀ b, b < 257 →
    (fastOk E1 E2 12 154 b && fastAnswer E1 E2 W2 12 154 b == (154 + b) % 257) = true := by
  decide +kernel

/-- Row 154 of the addition table: the network answers (154 + b) % 257 for every b. -/
theorem row_154 : ∀ b, b < 257 → answer 154 b = (154 + b) % 257 := by
  intro b hb
  have h := fast_154 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 154 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 154 b table_ok h.1, h.2]

theorem fast_155 : ∀ b, b < 257 →
    (fastOk E1 E2 12 155 b && fastAnswer E1 E2 W2 12 155 b == (155 + b) % 257) = true := by
  decide +kernel

/-- Row 155 of the addition table: the network answers (155 + b) % 257 for every b. -/
theorem row_155 : ∀ b, b < 257 → answer 155 b = (155 + b) % 257 := by
  intro b hb
  have h := fast_155 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 155 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 155 b table_ok h.1, h.2]

theorem fast_156 : ∀ b, b < 257 →
    (fastOk E1 E2 12 156 b && fastAnswer E1 E2 W2 12 156 b == (156 + b) % 257) = true := by
  decide +kernel

/-- Row 156 of the addition table: the network answers (156 + b) % 257 for every b. -/
theorem row_156 : ∀ b, b < 257 → answer 156 b = (156 + b) % 257 := by
  intro b hb
  have h := fast_156 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 156 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 156 b table_ok h.1, h.2]

theorem fast_157 : ∀ b, b < 257 →
    (fastOk E1 E2 12 157 b && fastAnswer E1 E2 W2 12 157 b == (157 + b) % 257) = true := by
  decide +kernel

/-- Row 157 of the addition table: the network answers (157 + b) % 257 for every b. -/
theorem row_157 : ∀ b, b < 257 → answer 157 b = (157 + b) % 257 := by
  intro b hb
  have h := fast_157 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 157 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 157 b table_ok h.1, h.2]

theorem fast_158 : ∀ b, b < 257 →
    (fastOk E1 E2 12 158 b && fastAnswer E1 E2 W2 12 158 b == (158 + b) % 257) = true := by
  decide +kernel

/-- Row 158 of the addition table: the network answers (158 + b) % 257 for every b. -/
theorem row_158 : ∀ b, b < 257 → answer 158 b = (158 + b) % 257 := by
  intro b hb
  have h := fast_158 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 158 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 158 b table_ok h.1, h.2]

theorem fast_159 : ∀ b, b < 257 →
    (fastOk E1 E2 12 159 b && fastAnswer E1 E2 W2 12 159 b == (159 + b) % 257) = true := by
  decide +kernel

/-- Row 159 of the addition table: the network answers (159 + b) % 257 for every b. -/
theorem row_159 : ∀ b, b < 257 → answer 159 b = (159 + b) % 257 := by
  intro b hb
  have h := fast_159 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 159 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 159 b table_ok h.1, h.2]

theorem fast_160 : ∀ b, b < 257 →
    (fastOk E1 E2 12 160 b && fastAnswer E1 E2 W2 12 160 b == (160 + b) % 257) = true := by
  decide +kernel

/-- Row 160 of the addition table: the network answers (160 + b) % 257 for every b. -/
theorem row_160 : ∀ b, b < 257 → answer 160 b = (160 + b) % 257 := by
  intro b hb
  have h := fast_160 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 160 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 160 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

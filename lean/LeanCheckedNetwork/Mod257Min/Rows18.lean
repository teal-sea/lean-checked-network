import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 145 to 152 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_145 : ∀ b, b < 257 →
    (fastOk E1 E2 12 145 b && fastAnswer E1 E2 W2 12 145 b == (145 + b) % 257) = true := by
  decide +kernel

/-- Row 145 of the addition table: the network answers (145 + b) % 257 for every b. -/
theorem row_145 : ∀ b, b < 257 → answer 145 b = (145 + b) % 257 := by
  intro b hb
  have h := fast_145 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 145 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 145 b table_ok h.1, h.2]

theorem fast_146 : ∀ b, b < 257 →
    (fastOk E1 E2 12 146 b && fastAnswer E1 E2 W2 12 146 b == (146 + b) % 257) = true := by
  decide +kernel

/-- Row 146 of the addition table: the network answers (146 + b) % 257 for every b. -/
theorem row_146 : ∀ b, b < 257 → answer 146 b = (146 + b) % 257 := by
  intro b hb
  have h := fast_146 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 146 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 146 b table_ok h.1, h.2]

theorem fast_147 : ∀ b, b < 257 →
    (fastOk E1 E2 12 147 b && fastAnswer E1 E2 W2 12 147 b == (147 + b) % 257) = true := by
  decide +kernel

/-- Row 147 of the addition table: the network answers (147 + b) % 257 for every b. -/
theorem row_147 : ∀ b, b < 257 → answer 147 b = (147 + b) % 257 := by
  intro b hb
  have h := fast_147 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 147 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 147 b table_ok h.1, h.2]

theorem fast_148 : ∀ b, b < 257 →
    (fastOk E1 E2 12 148 b && fastAnswer E1 E2 W2 12 148 b == (148 + b) % 257) = true := by
  decide +kernel

/-- Row 148 of the addition table: the network answers (148 + b) % 257 for every b. -/
theorem row_148 : ∀ b, b < 257 → answer 148 b = (148 + b) % 257 := by
  intro b hb
  have h := fast_148 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 148 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 148 b table_ok h.1, h.2]

theorem fast_149 : ∀ b, b < 257 →
    (fastOk E1 E2 12 149 b && fastAnswer E1 E2 W2 12 149 b == (149 + b) % 257) = true := by
  decide +kernel

/-- Row 149 of the addition table: the network answers (149 + b) % 257 for every b. -/
theorem row_149 : ∀ b, b < 257 → answer 149 b = (149 + b) % 257 := by
  intro b hb
  have h := fast_149 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 149 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 149 b table_ok h.1, h.2]

theorem fast_150 : ∀ b, b < 257 →
    (fastOk E1 E2 12 150 b && fastAnswer E1 E2 W2 12 150 b == (150 + b) % 257) = true := by
  decide +kernel

/-- Row 150 of the addition table: the network answers (150 + b) % 257 for every b. -/
theorem row_150 : ∀ b, b < 257 → answer 150 b = (150 + b) % 257 := by
  intro b hb
  have h := fast_150 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 150 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 150 b table_ok h.1, h.2]

theorem fast_151 : ∀ b, b < 257 →
    (fastOk E1 E2 12 151 b && fastAnswer E1 E2 W2 12 151 b == (151 + b) % 257) = true := by
  decide +kernel

/-- Row 151 of the addition table: the network answers (151 + b) % 257 for every b. -/
theorem row_151 : ∀ b, b < 257 → answer 151 b = (151 + b) % 257 := by
  intro b hb
  have h := fast_151 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 151 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 151 b table_ok h.1, h.2]

theorem fast_152 : ∀ b, b < 257 →
    (fastOk E1 E2 12 152 b && fastAnswer E1 E2 W2 12 152 b == (152 + b) % 257) = true := by
  decide +kernel

/-- Row 152 of the addition table: the network answers (152 + b) % 257 for every b. -/
theorem row_152 : ∀ b, b < 257 → answer 152 b = (152 + b) % 257 := by
  intro b hb
  have h := fast_152 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 152 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 152 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

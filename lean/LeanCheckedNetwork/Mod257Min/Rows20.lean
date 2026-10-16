import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 161 to 168 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_161 : ∀ b, b < 257 →
    (fastOk E1 E2 12 161 b && fastAnswer E1 E2 W2 12 161 b == (161 + b) % 257) = true := by
  decide +kernel

/-- Row 161 of the addition table: the network answers (161 + b) % 257 for every b. -/
theorem row_161 : ∀ b, b < 257 → answer 161 b = (161 + b) % 257 := by
  intro b hb
  have h := fast_161 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 161 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 161 b table_ok h.1, h.2]

theorem fast_162 : ∀ b, b < 257 →
    (fastOk E1 E2 12 162 b && fastAnswer E1 E2 W2 12 162 b == (162 + b) % 257) = true := by
  decide +kernel

/-- Row 162 of the addition table: the network answers (162 + b) % 257 for every b. -/
theorem row_162 : ∀ b, b < 257 → answer 162 b = (162 + b) % 257 := by
  intro b hb
  have h := fast_162 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 162 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 162 b table_ok h.1, h.2]

theorem fast_163 : ∀ b, b < 257 →
    (fastOk E1 E2 12 163 b && fastAnswer E1 E2 W2 12 163 b == (163 + b) % 257) = true := by
  decide +kernel

/-- Row 163 of the addition table: the network answers (163 + b) % 257 for every b. -/
theorem row_163 : ∀ b, b < 257 → answer 163 b = (163 + b) % 257 := by
  intro b hb
  have h := fast_163 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 163 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 163 b table_ok h.1, h.2]

theorem fast_164 : ∀ b, b < 257 →
    (fastOk E1 E2 12 164 b && fastAnswer E1 E2 W2 12 164 b == (164 + b) % 257) = true := by
  decide +kernel

/-- Row 164 of the addition table: the network answers (164 + b) % 257 for every b. -/
theorem row_164 : ∀ b, b < 257 → answer 164 b = (164 + b) % 257 := by
  intro b hb
  have h := fast_164 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 164 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 164 b table_ok h.1, h.2]

theorem fast_165 : ∀ b, b < 257 →
    (fastOk E1 E2 12 165 b && fastAnswer E1 E2 W2 12 165 b == (165 + b) % 257) = true := by
  decide +kernel

/-- Row 165 of the addition table: the network answers (165 + b) % 257 for every b. -/
theorem row_165 : ∀ b, b < 257 → answer 165 b = (165 + b) % 257 := by
  intro b hb
  have h := fast_165 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 165 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 165 b table_ok h.1, h.2]

theorem fast_166 : ∀ b, b < 257 →
    (fastOk E1 E2 12 166 b && fastAnswer E1 E2 W2 12 166 b == (166 + b) % 257) = true := by
  decide +kernel

/-- Row 166 of the addition table: the network answers (166 + b) % 257 for every b. -/
theorem row_166 : ∀ b, b < 257 → answer 166 b = (166 + b) % 257 := by
  intro b hb
  have h := fast_166 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 166 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 166 b table_ok h.1, h.2]

theorem fast_167 : ∀ b, b < 257 →
    (fastOk E1 E2 12 167 b && fastAnswer E1 E2 W2 12 167 b == (167 + b) % 257) = true := by
  decide +kernel

/-- Row 167 of the addition table: the network answers (167 + b) % 257 for every b. -/
theorem row_167 : ∀ b, b < 257 → answer 167 b = (167 + b) % 257 := by
  intro b hb
  have h := fast_167 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 167 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 167 b table_ok h.1, h.2]

theorem fast_168 : ∀ b, b < 257 →
    (fastOk E1 E2 12 168 b && fastAnswer E1 E2 W2 12 168 b == (168 + b) % 257) = true := by
  decide +kernel

/-- Row 168 of the addition table: the network answers (168 + b) % 257 for every b. -/
theorem row_168 : ∀ b, b < 257 → answer 168 b = (168 + b) % 257 := by
  intro b hb
  have h := fast_168 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 168 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 168 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

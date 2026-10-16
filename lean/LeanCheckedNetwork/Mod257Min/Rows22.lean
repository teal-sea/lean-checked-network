import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 177 to 184 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_177 : ∀ b, b < 257 →
    (fastOk E1 E2 12 177 b && fastAnswer E1 E2 W2 12 177 b == (177 + b) % 257) = true := by
  decide +kernel

/-- Row 177 of the addition table: the network answers (177 + b) % 257 for every b. -/
theorem row_177 : ∀ b, b < 257 → answer 177 b = (177 + b) % 257 := by
  intro b hb
  have h := fast_177 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 177 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 177 b table_ok h.1, h.2]

theorem fast_178 : ∀ b, b < 257 →
    (fastOk E1 E2 12 178 b && fastAnswer E1 E2 W2 12 178 b == (178 + b) % 257) = true := by
  decide +kernel

/-- Row 178 of the addition table: the network answers (178 + b) % 257 for every b. -/
theorem row_178 : ∀ b, b < 257 → answer 178 b = (178 + b) % 257 := by
  intro b hb
  have h := fast_178 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 178 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 178 b table_ok h.1, h.2]

theorem fast_179 : ∀ b, b < 257 →
    (fastOk E1 E2 12 179 b && fastAnswer E1 E2 W2 12 179 b == (179 + b) % 257) = true := by
  decide +kernel

/-- Row 179 of the addition table: the network answers (179 + b) % 257 for every b. -/
theorem row_179 : ∀ b, b < 257 → answer 179 b = (179 + b) % 257 := by
  intro b hb
  have h := fast_179 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 179 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 179 b table_ok h.1, h.2]

theorem fast_180 : ∀ b, b < 257 →
    (fastOk E1 E2 12 180 b && fastAnswer E1 E2 W2 12 180 b == (180 + b) % 257) = true := by
  decide +kernel

/-- Row 180 of the addition table: the network answers (180 + b) % 257 for every b. -/
theorem row_180 : ∀ b, b < 257 → answer 180 b = (180 + b) % 257 := by
  intro b hb
  have h := fast_180 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 180 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 180 b table_ok h.1, h.2]

theorem fast_181 : ∀ b, b < 257 →
    (fastOk E1 E2 12 181 b && fastAnswer E1 E2 W2 12 181 b == (181 + b) % 257) = true := by
  decide +kernel

/-- Row 181 of the addition table: the network answers (181 + b) % 257 for every b. -/
theorem row_181 : ∀ b, b < 257 → answer 181 b = (181 + b) % 257 := by
  intro b hb
  have h := fast_181 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 181 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 181 b table_ok h.1, h.2]

theorem fast_182 : ∀ b, b < 257 →
    (fastOk E1 E2 12 182 b && fastAnswer E1 E2 W2 12 182 b == (182 + b) % 257) = true := by
  decide +kernel

/-- Row 182 of the addition table: the network answers (182 + b) % 257 for every b. -/
theorem row_182 : ∀ b, b < 257 → answer 182 b = (182 + b) % 257 := by
  intro b hb
  have h := fast_182 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 182 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 182 b table_ok h.1, h.2]

theorem fast_183 : ∀ b, b < 257 →
    (fastOk E1 E2 12 183 b && fastAnswer E1 E2 W2 12 183 b == (183 + b) % 257) = true := by
  decide +kernel

/-- Row 183 of the addition table: the network answers (183 + b) % 257 for every b. -/
theorem row_183 : ∀ b, b < 257 → answer 183 b = (183 + b) % 257 := by
  intro b hb
  have h := fast_183 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 183 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 183 b table_ok h.1, h.2]

theorem fast_184 : ∀ b, b < 257 →
    (fastOk E1 E2 12 184 b && fastAnswer E1 E2 W2 12 184 b == (184 + b) % 257) = true := by
  decide +kernel

/-- Row 184 of the addition table: the network answers (184 + b) % 257 for every b. -/
theorem row_184 : ∀ b, b < 257 → answer 184 b = (184 + b) % 257 := by
  intro b hb
  have h := fast_184 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 184 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 184 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 225 to 232 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_225 : ∀ b, b < 257 →
    (fastOk E1 E2 12 225 b && fastAnswer E1 E2 W2 12 225 b == (225 + b) % 257) = true := by
  decide +kernel

/-- Row 225 of the addition table: the network answers (225 + b) % 257 for every b. -/
theorem row_225 : ∀ b, b < 257 → answer 225 b = (225 + b) % 257 := by
  intro b hb
  have h := fast_225 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 225 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 225 b table_ok h.1, h.2]

theorem fast_226 : ∀ b, b < 257 →
    (fastOk E1 E2 12 226 b && fastAnswer E1 E2 W2 12 226 b == (226 + b) % 257) = true := by
  decide +kernel

/-- Row 226 of the addition table: the network answers (226 + b) % 257 for every b. -/
theorem row_226 : ∀ b, b < 257 → answer 226 b = (226 + b) % 257 := by
  intro b hb
  have h := fast_226 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 226 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 226 b table_ok h.1, h.2]

theorem fast_227 : ∀ b, b < 257 →
    (fastOk E1 E2 12 227 b && fastAnswer E1 E2 W2 12 227 b == (227 + b) % 257) = true := by
  decide +kernel

/-- Row 227 of the addition table: the network answers (227 + b) % 257 for every b. -/
theorem row_227 : ∀ b, b < 257 → answer 227 b = (227 + b) % 257 := by
  intro b hb
  have h := fast_227 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 227 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 227 b table_ok h.1, h.2]

theorem fast_228 : ∀ b, b < 257 →
    (fastOk E1 E2 12 228 b && fastAnswer E1 E2 W2 12 228 b == (228 + b) % 257) = true := by
  decide +kernel

/-- Row 228 of the addition table: the network answers (228 + b) % 257 for every b. -/
theorem row_228 : ∀ b, b < 257 → answer 228 b = (228 + b) % 257 := by
  intro b hb
  have h := fast_228 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 228 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 228 b table_ok h.1, h.2]

theorem fast_229 : ∀ b, b < 257 →
    (fastOk E1 E2 12 229 b && fastAnswer E1 E2 W2 12 229 b == (229 + b) % 257) = true := by
  decide +kernel

/-- Row 229 of the addition table: the network answers (229 + b) % 257 for every b. -/
theorem row_229 : ∀ b, b < 257 → answer 229 b = (229 + b) % 257 := by
  intro b hb
  have h := fast_229 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 229 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 229 b table_ok h.1, h.2]

theorem fast_230 : ∀ b, b < 257 →
    (fastOk E1 E2 12 230 b && fastAnswer E1 E2 W2 12 230 b == (230 + b) % 257) = true := by
  decide +kernel

/-- Row 230 of the addition table: the network answers (230 + b) % 257 for every b. -/
theorem row_230 : ∀ b, b < 257 → answer 230 b = (230 + b) % 257 := by
  intro b hb
  have h := fast_230 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 230 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 230 b table_ok h.1, h.2]

theorem fast_231 : ∀ b, b < 257 →
    (fastOk E1 E2 12 231 b && fastAnswer E1 E2 W2 12 231 b == (231 + b) % 257) = true := by
  decide +kernel

/-- Row 231 of the addition table: the network answers (231 + b) % 257 for every b. -/
theorem row_231 : ∀ b, b < 257 → answer 231 b = (231 + b) % 257 := by
  intro b hb
  have h := fast_231 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 231 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 231 b table_ok h.1, h.2]

theorem fast_232 : ∀ b, b < 257 →
    (fastOk E1 E2 12 232 b && fastAnswer E1 E2 W2 12 232 b == (232 + b) % 257) = true := by
  decide +kernel

/-- Row 232 of the addition table: the network answers (232 + b) % 257 for every b. -/
theorem row_232 : ∀ b, b < 257 → answer 232 b = (232 + b) % 257 := by
  intro b hb
  have h := fast_232 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 232 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 232 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

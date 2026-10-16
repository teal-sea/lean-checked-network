import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 225 to 240 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

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

theorem fast_233 : ∀ b, b < 257 →
    (fastOk E1 E2 12 233 b && fastAnswer E1 E2 W2 12 233 b == (233 + b) % 257) = true := by
  decide +kernel

/-- Row 233 of the addition table: the network answers (233 + b) % 257 for every b. -/
theorem row_233 : ∀ b, b < 257 → answer 233 b = (233 + b) % 257 := by
  intro b hb
  have h := fast_233 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 233 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 233 b table_ok h.1, h.2]

theorem fast_234 : ∀ b, b < 257 →
    (fastOk E1 E2 12 234 b && fastAnswer E1 E2 W2 12 234 b == (234 + b) % 257) = true := by
  decide +kernel

/-- Row 234 of the addition table: the network answers (234 + b) % 257 for every b. -/
theorem row_234 : ∀ b, b < 257 → answer 234 b = (234 + b) % 257 := by
  intro b hb
  have h := fast_234 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 234 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 234 b table_ok h.1, h.2]

theorem fast_235 : ∀ b, b < 257 →
    (fastOk E1 E2 12 235 b && fastAnswer E1 E2 W2 12 235 b == (235 + b) % 257) = true := by
  decide +kernel

/-- Row 235 of the addition table: the network answers (235 + b) % 257 for every b. -/
theorem row_235 : ∀ b, b < 257 → answer 235 b = (235 + b) % 257 := by
  intro b hb
  have h := fast_235 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 235 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 235 b table_ok h.1, h.2]

theorem fast_236 : ∀ b, b < 257 →
    (fastOk E1 E2 12 236 b && fastAnswer E1 E2 W2 12 236 b == (236 + b) % 257) = true := by
  decide +kernel

/-- Row 236 of the addition table: the network answers (236 + b) % 257 for every b. -/
theorem row_236 : ∀ b, b < 257 → answer 236 b = (236 + b) % 257 := by
  intro b hb
  have h := fast_236 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 236 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 236 b table_ok h.1, h.2]

theorem fast_237 : ∀ b, b < 257 →
    (fastOk E1 E2 12 237 b && fastAnswer E1 E2 W2 12 237 b == (237 + b) % 257) = true := by
  decide +kernel

/-- Row 237 of the addition table: the network answers (237 + b) % 257 for every b. -/
theorem row_237 : ∀ b, b < 257 → answer 237 b = (237 + b) % 257 := by
  intro b hb
  have h := fast_237 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 237 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 237 b table_ok h.1, h.2]

theorem fast_238 : ∀ b, b < 257 →
    (fastOk E1 E2 12 238 b && fastAnswer E1 E2 W2 12 238 b == (238 + b) % 257) = true := by
  decide +kernel

/-- Row 238 of the addition table: the network answers (238 + b) % 257 for every b. -/
theorem row_238 : ∀ b, b < 257 → answer 238 b = (238 + b) % 257 := by
  intro b hb
  have h := fast_238 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 238 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 238 b table_ok h.1, h.2]

theorem fast_239 : ∀ b, b < 257 →
    (fastOk E1 E2 12 239 b && fastAnswer E1 E2 W2 12 239 b == (239 + b) % 257) = true := by
  decide +kernel

/-- Row 239 of the addition table: the network answers (239 + b) % 257 for every b. -/
theorem row_239 : ∀ b, b < 257 → answer 239 b = (239 + b) % 257 := by
  intro b hb
  have h := fast_239 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 239 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 239 b table_ok h.1, h.2]

theorem fast_240 : ∀ b, b < 257 →
    (fastOk E1 E2 12 240 b && fastAnswer E1 E2 W2 12 240 b == (240 + b) % 257) = true := by
  decide +kernel

/-- Row 240 of the addition table: the network answers (240 + b) % 257 for every b. -/
theorem row_240 : ∀ b, b < 257 → answer 240 b = (240 + b) % 257 := by
  intro b hb
  have h := fast_240 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 240 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 240 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

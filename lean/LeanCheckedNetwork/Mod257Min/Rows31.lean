import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 249 to 256 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_249 : ∀ b, b < 257 →
    (fastOk E1 E2 12 249 b && fastAnswer E1 E2 W2 12 249 b == (249 + b) % 257) = true := by
  decide +kernel

/-- Row 249 of the addition table: the network answers (249 + b) % 257 for every b. -/
theorem row_249 : ∀ b, b < 257 → answer 249 b = (249 + b) % 257 := by
  intro b hb
  have h := fast_249 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 249 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 249 b table_ok h.1, h.2]

theorem fast_250 : ∀ b, b < 257 →
    (fastOk E1 E2 12 250 b && fastAnswer E1 E2 W2 12 250 b == (250 + b) % 257) = true := by
  decide +kernel

/-- Row 250 of the addition table: the network answers (250 + b) % 257 for every b. -/
theorem row_250 : ∀ b, b < 257 → answer 250 b = (250 + b) % 257 := by
  intro b hb
  have h := fast_250 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 250 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 250 b table_ok h.1, h.2]

theorem fast_251 : ∀ b, b < 257 →
    (fastOk E1 E2 12 251 b && fastAnswer E1 E2 W2 12 251 b == (251 + b) % 257) = true := by
  decide +kernel

/-- Row 251 of the addition table: the network answers (251 + b) % 257 for every b. -/
theorem row_251 : ∀ b, b < 257 → answer 251 b = (251 + b) % 257 := by
  intro b hb
  have h := fast_251 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 251 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 251 b table_ok h.1, h.2]

theorem fast_252 : ∀ b, b < 257 →
    (fastOk E1 E2 12 252 b && fastAnswer E1 E2 W2 12 252 b == (252 + b) % 257) = true := by
  decide +kernel

/-- Row 252 of the addition table: the network answers (252 + b) % 257 for every b. -/
theorem row_252 : ∀ b, b < 257 → answer 252 b = (252 + b) % 257 := by
  intro b hb
  have h := fast_252 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 252 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 252 b table_ok h.1, h.2]

theorem fast_253 : ∀ b, b < 257 →
    (fastOk E1 E2 12 253 b && fastAnswer E1 E2 W2 12 253 b == (253 + b) % 257) = true := by
  decide +kernel

/-- Row 253 of the addition table: the network answers (253 + b) % 257 for every b. -/
theorem row_253 : ∀ b, b < 257 → answer 253 b = (253 + b) % 257 := by
  intro b hb
  have h := fast_253 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 253 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 253 b table_ok h.1, h.2]

theorem fast_254 : ∀ b, b < 257 →
    (fastOk E1 E2 12 254 b && fastAnswer E1 E2 W2 12 254 b == (254 + b) % 257) = true := by
  decide +kernel

/-- Row 254 of the addition table: the network answers (254 + b) % 257 for every b. -/
theorem row_254 : ∀ b, b < 257 → answer 254 b = (254 + b) % 257 := by
  intro b hb
  have h := fast_254 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 254 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 254 b table_ok h.1, h.2]

theorem fast_255 : ∀ b, b < 257 →
    (fastOk E1 E2 12 255 b && fastAnswer E1 E2 W2 12 255 b == (255 + b) % 257) = true := by
  decide +kernel

/-- Row 255 of the addition table: the network answers (255 + b) % 257 for every b. -/
theorem row_255 : ∀ b, b < 257 → answer 255 b = (255 + b) % 257 := by
  intro b hb
  have h := fast_255 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 255 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 255 b table_ok h.1, h.2]

theorem fast_256 : ∀ b, b < 257 →
    (fastOk E1 E2 12 256 b && fastAnswer E1 E2 W2 12 256 b == (256 + b) % 257) = true := by
  decide +kernel

/-- Row 256 of the addition table: the network answers (256 + b) % 257 for every b. -/
theorem row_256 : ∀ b, b < 257 → answer 256 b = (256 + b) % 257 := by
  intro b hb
  have h := fast_256 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 256 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 256 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

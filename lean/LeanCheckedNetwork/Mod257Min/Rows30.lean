import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 241 to 248 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_241 : ∀ b, b < 257 →
    (fastOk E1 E2 12 241 b && fastAnswer E1 E2 W2 12 241 b == (241 + b) % 257) = true := by
  decide +kernel

/-- Row 241 of the addition table: the network answers (241 + b) % 257 for every b. -/
theorem row_241 : ∀ b, b < 257 → answer 241 b = (241 + b) % 257 := by
  intro b hb
  have h := fast_241 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 241 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 241 b table_ok h.1, h.2]

theorem fast_242 : ∀ b, b < 257 →
    (fastOk E1 E2 12 242 b && fastAnswer E1 E2 W2 12 242 b == (242 + b) % 257) = true := by
  decide +kernel

/-- Row 242 of the addition table: the network answers (242 + b) % 257 for every b. -/
theorem row_242 : ∀ b, b < 257 → answer 242 b = (242 + b) % 257 := by
  intro b hb
  have h := fast_242 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 242 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 242 b table_ok h.1, h.2]

theorem fast_243 : ∀ b, b < 257 →
    (fastOk E1 E2 12 243 b && fastAnswer E1 E2 W2 12 243 b == (243 + b) % 257) = true := by
  decide +kernel

/-- Row 243 of the addition table: the network answers (243 + b) % 257 for every b. -/
theorem row_243 : ∀ b, b < 257 → answer 243 b = (243 + b) % 257 := by
  intro b hb
  have h := fast_243 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 243 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 243 b table_ok h.1, h.2]

theorem fast_244 : ∀ b, b < 257 →
    (fastOk E1 E2 12 244 b && fastAnswer E1 E2 W2 12 244 b == (244 + b) % 257) = true := by
  decide +kernel

/-- Row 244 of the addition table: the network answers (244 + b) % 257 for every b. -/
theorem row_244 : ∀ b, b < 257 → answer 244 b = (244 + b) % 257 := by
  intro b hb
  have h := fast_244 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 244 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 244 b table_ok h.1, h.2]

theorem fast_245 : ∀ b, b < 257 →
    (fastOk E1 E2 12 245 b && fastAnswer E1 E2 W2 12 245 b == (245 + b) % 257) = true := by
  decide +kernel

/-- Row 245 of the addition table: the network answers (245 + b) % 257 for every b. -/
theorem row_245 : ∀ b, b < 257 → answer 245 b = (245 + b) % 257 := by
  intro b hb
  have h := fast_245 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 245 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 245 b table_ok h.1, h.2]

theorem fast_246 : ∀ b, b < 257 →
    (fastOk E1 E2 12 246 b && fastAnswer E1 E2 W2 12 246 b == (246 + b) % 257) = true := by
  decide +kernel

/-- Row 246 of the addition table: the network answers (246 + b) % 257 for every b. -/
theorem row_246 : ∀ b, b < 257 → answer 246 b = (246 + b) % 257 := by
  intro b hb
  have h := fast_246 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 246 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 246 b table_ok h.1, h.2]

theorem fast_247 : ∀ b, b < 257 →
    (fastOk E1 E2 12 247 b && fastAnswer E1 E2 W2 12 247 b == (247 + b) % 257) = true := by
  decide +kernel

/-- Row 247 of the addition table: the network answers (247 + b) % 257 for every b. -/
theorem row_247 : ∀ b, b < 257 → answer 247 b = (247 + b) % 257 := by
  intro b hb
  have h := fast_247 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 247 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 247 b table_ok h.1, h.2]

theorem fast_248 : ∀ b, b < 257 →
    (fastOk E1 E2 12 248 b && fastAnswer E1 E2 W2 12 248 b == (248 + b) % 257) = true := by
  decide +kernel

/-- Row 248 of the addition table: the network answers (248 + b) % 257 for every b. -/
theorem row_248 : ∀ b, b < 257 → answer 248 b = (248 + b) % 257 := by
  intro b hb
  have h := fast_248 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 248 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 248 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

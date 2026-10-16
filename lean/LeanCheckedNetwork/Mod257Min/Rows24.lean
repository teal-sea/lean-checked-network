import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 193 to 200 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_193 : ∀ b, b < 257 →
    (fastOk E1 E2 12 193 b && fastAnswer E1 E2 W2 12 193 b == (193 + b) % 257) = true := by
  decide +kernel

/-- Row 193 of the addition table: the network answers (193 + b) % 257 for every b. -/
theorem row_193 : ∀ b, b < 257 → answer 193 b = (193 + b) % 257 := by
  intro b hb
  have h := fast_193 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 193 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 193 b table_ok h.1, h.2]

theorem fast_194 : ∀ b, b < 257 →
    (fastOk E1 E2 12 194 b && fastAnswer E1 E2 W2 12 194 b == (194 + b) % 257) = true := by
  decide +kernel

/-- Row 194 of the addition table: the network answers (194 + b) % 257 for every b. -/
theorem row_194 : ∀ b, b < 257 → answer 194 b = (194 + b) % 257 := by
  intro b hb
  have h := fast_194 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 194 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 194 b table_ok h.1, h.2]

theorem fast_195 : ∀ b, b < 257 →
    (fastOk E1 E2 12 195 b && fastAnswer E1 E2 W2 12 195 b == (195 + b) % 257) = true := by
  decide +kernel

/-- Row 195 of the addition table: the network answers (195 + b) % 257 for every b. -/
theorem row_195 : ∀ b, b < 257 → answer 195 b = (195 + b) % 257 := by
  intro b hb
  have h := fast_195 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 195 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 195 b table_ok h.1, h.2]

theorem fast_196 : ∀ b, b < 257 →
    (fastOk E1 E2 12 196 b && fastAnswer E1 E2 W2 12 196 b == (196 + b) % 257) = true := by
  decide +kernel

/-- Row 196 of the addition table: the network answers (196 + b) % 257 for every b. -/
theorem row_196 : ∀ b, b < 257 → answer 196 b = (196 + b) % 257 := by
  intro b hb
  have h := fast_196 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 196 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 196 b table_ok h.1, h.2]

theorem fast_197 : ∀ b, b < 257 →
    (fastOk E1 E2 12 197 b && fastAnswer E1 E2 W2 12 197 b == (197 + b) % 257) = true := by
  decide +kernel

/-- Row 197 of the addition table: the network answers (197 + b) % 257 for every b. -/
theorem row_197 : ∀ b, b < 257 → answer 197 b = (197 + b) % 257 := by
  intro b hb
  have h := fast_197 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 197 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 197 b table_ok h.1, h.2]

theorem fast_198 : ∀ b, b < 257 →
    (fastOk E1 E2 12 198 b && fastAnswer E1 E2 W2 12 198 b == (198 + b) % 257) = true := by
  decide +kernel

/-- Row 198 of the addition table: the network answers (198 + b) % 257 for every b. -/
theorem row_198 : ∀ b, b < 257 → answer 198 b = (198 + b) % 257 := by
  intro b hb
  have h := fast_198 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 198 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 198 b table_ok h.1, h.2]

theorem fast_199 : ∀ b, b < 257 →
    (fastOk E1 E2 12 199 b && fastAnswer E1 E2 W2 12 199 b == (199 + b) % 257) = true := by
  decide +kernel

/-- Row 199 of the addition table: the network answers (199 + b) % 257 for every b. -/
theorem row_199 : ∀ b, b < 257 → answer 199 b = (199 + b) % 257 := by
  intro b hb
  have h := fast_199 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 199 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 199 b table_ok h.1, h.2]

theorem fast_200 : ∀ b, b < 257 →
    (fastOk E1 E2 12 200 b && fastAnswer E1 E2 W2 12 200 b == (200 + b) % 257) = true := by
  decide +kernel

/-- Row 200 of the addition table: the network answers (200 + b) % 257 for every b. -/
theorem row_200 : ∀ b, b < 257 → answer 200 b = (200 + b) % 257 := by
  intro b hb
  have h := fast_200 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 200 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 200 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

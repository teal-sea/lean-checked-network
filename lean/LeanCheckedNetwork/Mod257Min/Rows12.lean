import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 193 to 208 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

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

theorem fast_201 : ∀ b, b < 257 →
    (fastOk E1 E2 12 201 b && fastAnswer E1 E2 W2 12 201 b == (201 + b) % 257) = true := by
  decide +kernel

/-- Row 201 of the addition table: the network answers (201 + b) % 257 for every b. -/
theorem row_201 : ∀ b, b < 257 → answer 201 b = (201 + b) % 257 := by
  intro b hb
  have h := fast_201 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 201 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 201 b table_ok h.1, h.2]

theorem fast_202 : ∀ b, b < 257 →
    (fastOk E1 E2 12 202 b && fastAnswer E1 E2 W2 12 202 b == (202 + b) % 257) = true := by
  decide +kernel

/-- Row 202 of the addition table: the network answers (202 + b) % 257 for every b. -/
theorem row_202 : ∀ b, b < 257 → answer 202 b = (202 + b) % 257 := by
  intro b hb
  have h := fast_202 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 202 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 202 b table_ok h.1, h.2]

theorem fast_203 : ∀ b, b < 257 →
    (fastOk E1 E2 12 203 b && fastAnswer E1 E2 W2 12 203 b == (203 + b) % 257) = true := by
  decide +kernel

/-- Row 203 of the addition table: the network answers (203 + b) % 257 for every b. -/
theorem row_203 : ∀ b, b < 257 → answer 203 b = (203 + b) % 257 := by
  intro b hb
  have h := fast_203 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 203 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 203 b table_ok h.1, h.2]

theorem fast_204 : ∀ b, b < 257 →
    (fastOk E1 E2 12 204 b && fastAnswer E1 E2 W2 12 204 b == (204 + b) % 257) = true := by
  decide +kernel

/-- Row 204 of the addition table: the network answers (204 + b) % 257 for every b. -/
theorem row_204 : ∀ b, b < 257 → answer 204 b = (204 + b) % 257 := by
  intro b hb
  have h := fast_204 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 204 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 204 b table_ok h.1, h.2]

theorem fast_205 : ∀ b, b < 257 →
    (fastOk E1 E2 12 205 b && fastAnswer E1 E2 W2 12 205 b == (205 + b) % 257) = true := by
  decide +kernel

/-- Row 205 of the addition table: the network answers (205 + b) % 257 for every b. -/
theorem row_205 : ∀ b, b < 257 → answer 205 b = (205 + b) % 257 := by
  intro b hb
  have h := fast_205 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 205 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 205 b table_ok h.1, h.2]

theorem fast_206 : ∀ b, b < 257 →
    (fastOk E1 E2 12 206 b && fastAnswer E1 E2 W2 12 206 b == (206 + b) % 257) = true := by
  decide +kernel

/-- Row 206 of the addition table: the network answers (206 + b) % 257 for every b. -/
theorem row_206 : ∀ b, b < 257 → answer 206 b = (206 + b) % 257 := by
  intro b hb
  have h := fast_206 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 206 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 206 b table_ok h.1, h.2]

theorem fast_207 : ∀ b, b < 257 →
    (fastOk E1 E2 12 207 b && fastAnswer E1 E2 W2 12 207 b == (207 + b) % 257) = true := by
  decide +kernel

/-- Row 207 of the addition table: the network answers (207 + b) % 257 for every b. -/
theorem row_207 : ∀ b, b < 257 → answer 207 b = (207 + b) % 257 := by
  intro b hb
  have h := fast_207 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 207 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 207 b table_ok h.1, h.2]

theorem fast_208 : ∀ b, b < 257 →
    (fastOk E1 E2 12 208 b && fastAnswer E1 E2 W2 12 208 b == (208 + b) % 257) = true := by
  decide +kernel

/-- Row 208 of the addition table: the network answers (208 + b) % 257 for every b. -/
theorem row_208 : ∀ b, b < 257 → answer 208 b = (208 + b) % 257 := by
  intro b hb
  have h := fast_208 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 208 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 208 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

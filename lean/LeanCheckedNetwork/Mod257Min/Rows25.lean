import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 201 to 208 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

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

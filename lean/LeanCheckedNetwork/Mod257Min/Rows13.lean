import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 209 to 224 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_209 : ∀ b, b < 257 →
    (fastOk E1 E2 12 209 b && fastAnswer E1 E2 W2 12 209 b == (209 + b) % 257) = true := by
  decide +kernel

/-- Row 209 of the addition table: the network answers (209 + b) % 257 for every b. -/
theorem row_209 : ∀ b, b < 257 → answer 209 b = (209 + b) % 257 := by
  intro b hb
  have h := fast_209 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 209 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 209 b table_ok h.1, h.2]

theorem fast_210 : ∀ b, b < 257 →
    (fastOk E1 E2 12 210 b && fastAnswer E1 E2 W2 12 210 b == (210 + b) % 257) = true := by
  decide +kernel

/-- Row 210 of the addition table: the network answers (210 + b) % 257 for every b. -/
theorem row_210 : ∀ b, b < 257 → answer 210 b = (210 + b) % 257 := by
  intro b hb
  have h := fast_210 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 210 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 210 b table_ok h.1, h.2]

theorem fast_211 : ∀ b, b < 257 →
    (fastOk E1 E2 12 211 b && fastAnswer E1 E2 W2 12 211 b == (211 + b) % 257) = true := by
  decide +kernel

/-- Row 211 of the addition table: the network answers (211 + b) % 257 for every b. -/
theorem row_211 : ∀ b, b < 257 → answer 211 b = (211 + b) % 257 := by
  intro b hb
  have h := fast_211 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 211 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 211 b table_ok h.1, h.2]

theorem fast_212 : ∀ b, b < 257 →
    (fastOk E1 E2 12 212 b && fastAnswer E1 E2 W2 12 212 b == (212 + b) % 257) = true := by
  decide +kernel

/-- Row 212 of the addition table: the network answers (212 + b) % 257 for every b. -/
theorem row_212 : ∀ b, b < 257 → answer 212 b = (212 + b) % 257 := by
  intro b hb
  have h := fast_212 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 212 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 212 b table_ok h.1, h.2]

theorem fast_213 : ∀ b, b < 257 →
    (fastOk E1 E2 12 213 b && fastAnswer E1 E2 W2 12 213 b == (213 + b) % 257) = true := by
  decide +kernel

/-- Row 213 of the addition table: the network answers (213 + b) % 257 for every b. -/
theorem row_213 : ∀ b, b < 257 → answer 213 b = (213 + b) % 257 := by
  intro b hb
  have h := fast_213 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 213 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 213 b table_ok h.1, h.2]

theorem fast_214 : ∀ b, b < 257 →
    (fastOk E1 E2 12 214 b && fastAnswer E1 E2 W2 12 214 b == (214 + b) % 257) = true := by
  decide +kernel

/-- Row 214 of the addition table: the network answers (214 + b) % 257 for every b. -/
theorem row_214 : ∀ b, b < 257 → answer 214 b = (214 + b) % 257 := by
  intro b hb
  have h := fast_214 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 214 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 214 b table_ok h.1, h.2]

theorem fast_215 : ∀ b, b < 257 →
    (fastOk E1 E2 12 215 b && fastAnswer E1 E2 W2 12 215 b == (215 + b) % 257) = true := by
  decide +kernel

/-- Row 215 of the addition table: the network answers (215 + b) % 257 for every b. -/
theorem row_215 : ∀ b, b < 257 → answer 215 b = (215 + b) % 257 := by
  intro b hb
  have h := fast_215 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 215 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 215 b table_ok h.1, h.2]

theorem fast_216 : ∀ b, b < 257 →
    (fastOk E1 E2 12 216 b && fastAnswer E1 E2 W2 12 216 b == (216 + b) % 257) = true := by
  decide +kernel

/-- Row 216 of the addition table: the network answers (216 + b) % 257 for every b. -/
theorem row_216 : ∀ b, b < 257 → answer 216 b = (216 + b) % 257 := by
  intro b hb
  have h := fast_216 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 216 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 216 b table_ok h.1, h.2]

theorem fast_217 : ∀ b, b < 257 →
    (fastOk E1 E2 12 217 b && fastAnswer E1 E2 W2 12 217 b == (217 + b) % 257) = true := by
  decide +kernel

/-- Row 217 of the addition table: the network answers (217 + b) % 257 for every b. -/
theorem row_217 : ∀ b, b < 257 → answer 217 b = (217 + b) % 257 := by
  intro b hb
  have h := fast_217 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 217 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 217 b table_ok h.1, h.2]

theorem fast_218 : ∀ b, b < 257 →
    (fastOk E1 E2 12 218 b && fastAnswer E1 E2 W2 12 218 b == (218 + b) % 257) = true := by
  decide +kernel

/-- Row 218 of the addition table: the network answers (218 + b) % 257 for every b. -/
theorem row_218 : ∀ b, b < 257 → answer 218 b = (218 + b) % 257 := by
  intro b hb
  have h := fast_218 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 218 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 218 b table_ok h.1, h.2]

theorem fast_219 : ∀ b, b < 257 →
    (fastOk E1 E2 12 219 b && fastAnswer E1 E2 W2 12 219 b == (219 + b) % 257) = true := by
  decide +kernel

/-- Row 219 of the addition table: the network answers (219 + b) % 257 for every b. -/
theorem row_219 : ∀ b, b < 257 → answer 219 b = (219 + b) % 257 := by
  intro b hb
  have h := fast_219 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 219 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 219 b table_ok h.1, h.2]

theorem fast_220 : ∀ b, b < 257 →
    (fastOk E1 E2 12 220 b && fastAnswer E1 E2 W2 12 220 b == (220 + b) % 257) = true := by
  decide +kernel

/-- Row 220 of the addition table: the network answers (220 + b) % 257 for every b. -/
theorem row_220 : ∀ b, b < 257 → answer 220 b = (220 + b) % 257 := by
  intro b hb
  have h := fast_220 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 220 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 220 b table_ok h.1, h.2]

theorem fast_221 : ∀ b, b < 257 →
    (fastOk E1 E2 12 221 b && fastAnswer E1 E2 W2 12 221 b == (221 + b) % 257) = true := by
  decide +kernel

/-- Row 221 of the addition table: the network answers (221 + b) % 257 for every b. -/
theorem row_221 : ∀ b, b < 257 → answer 221 b = (221 + b) % 257 := by
  intro b hb
  have h := fast_221 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 221 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 221 b table_ok h.1, h.2]

theorem fast_222 : ∀ b, b < 257 →
    (fastOk E1 E2 12 222 b && fastAnswer E1 E2 W2 12 222 b == (222 + b) % 257) = true := by
  decide +kernel

/-- Row 222 of the addition table: the network answers (222 + b) % 257 for every b. -/
theorem row_222 : ∀ b, b < 257 → answer 222 b = (222 + b) % 257 := by
  intro b hb
  have h := fast_222 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 222 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 222 b table_ok h.1, h.2]

theorem fast_223 : ∀ b, b < 257 →
    (fastOk E1 E2 12 223 b && fastAnswer E1 E2 W2 12 223 b == (223 + b) % 257) = true := by
  decide +kernel

/-- Row 223 of the addition table: the network answers (223 + b) % 257 for every b. -/
theorem row_223 : ∀ b, b < 257 → answer 223 b = (223 + b) % 257 := by
  intro b hb
  have h := fast_223 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 223 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 223 b table_ok h.1, h.2]

theorem fast_224 : ∀ b, b < 257 →
    (fastOk E1 E2 12 224 b && fastAnswer E1 E2 W2 12 224 b == (224 + b) % 257) = true := by
  decide +kernel

/-- Row 224 of the addition table: the network answers (224 + b) % 257 for every b. -/
theorem row_224 : ∀ b, b < 257 → answer 224 b = (224 + b) % 257 := by
  intro b hb
  have h := fast_224 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 224 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 224 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

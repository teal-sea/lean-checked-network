import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 89 to 96 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_89 : ∀ b, b < 257 →
    (fastOk E1 E2 12 89 b && fastAnswer E1 E2 W2 12 89 b == (89 + b) % 257) = true := by
  decide +kernel

/-- Row 89 of the addition table: the network answers (89 + b) % 257 for every b. -/
theorem row_89 : ∀ b, b < 257 → answer 89 b = (89 + b) % 257 := by
  intro b hb
  have h := fast_89 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 89 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 89 b table_ok h.1, h.2]

theorem fast_90 : ∀ b, b < 257 →
    (fastOk E1 E2 12 90 b && fastAnswer E1 E2 W2 12 90 b == (90 + b) % 257) = true := by
  decide +kernel

/-- Row 90 of the addition table: the network answers (90 + b) % 257 for every b. -/
theorem row_90 : ∀ b, b < 257 → answer 90 b = (90 + b) % 257 := by
  intro b hb
  have h := fast_90 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 90 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 90 b table_ok h.1, h.2]

theorem fast_91 : ∀ b, b < 257 →
    (fastOk E1 E2 12 91 b && fastAnswer E1 E2 W2 12 91 b == (91 + b) % 257) = true := by
  decide +kernel

/-- Row 91 of the addition table: the network answers (91 + b) % 257 for every b. -/
theorem row_91 : ∀ b, b < 257 → answer 91 b = (91 + b) % 257 := by
  intro b hb
  have h := fast_91 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 91 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 91 b table_ok h.1, h.2]

theorem fast_92 : ∀ b, b < 257 →
    (fastOk E1 E2 12 92 b && fastAnswer E1 E2 W2 12 92 b == (92 + b) % 257) = true := by
  decide +kernel

/-- Row 92 of the addition table: the network answers (92 + b) % 257 for every b. -/
theorem row_92 : ∀ b, b < 257 → answer 92 b = (92 + b) % 257 := by
  intro b hb
  have h := fast_92 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 92 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 92 b table_ok h.1, h.2]

theorem fast_93 : ∀ b, b < 257 →
    (fastOk E1 E2 12 93 b && fastAnswer E1 E2 W2 12 93 b == (93 + b) % 257) = true := by
  decide +kernel

/-- Row 93 of the addition table: the network answers (93 + b) % 257 for every b. -/
theorem row_93 : ∀ b, b < 257 → answer 93 b = (93 + b) % 257 := by
  intro b hb
  have h := fast_93 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 93 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 93 b table_ok h.1, h.2]

theorem fast_94 : ∀ b, b < 257 →
    (fastOk E1 E2 12 94 b && fastAnswer E1 E2 W2 12 94 b == (94 + b) % 257) = true := by
  decide +kernel

/-- Row 94 of the addition table: the network answers (94 + b) % 257 for every b. -/
theorem row_94 : ∀ b, b < 257 → answer 94 b = (94 + b) % 257 := by
  intro b hb
  have h := fast_94 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 94 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 94 b table_ok h.1, h.2]

theorem fast_95 : ∀ b, b < 257 →
    (fastOk E1 E2 12 95 b && fastAnswer E1 E2 W2 12 95 b == (95 + b) % 257) = true := by
  decide +kernel

/-- Row 95 of the addition table: the network answers (95 + b) % 257 for every b. -/
theorem row_95 : ∀ b, b < 257 → answer 95 b = (95 + b) % 257 := by
  intro b hb
  have h := fast_95 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 95 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 95 b table_ok h.1, h.2]

theorem fast_96 : ∀ b, b < 257 →
    (fastOk E1 E2 12 96 b && fastAnswer E1 E2 W2 12 96 b == (96 + b) % 257) = true := by
  decide +kernel

/-- Row 96 of the addition table: the network answers (96 + b) % 257 for every b. -/
theorem row_96 : ∀ b, b < 257 → answer 96 b = (96 + b) % 257 := by
  intro b hb
  have h := fast_96 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 96 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 96 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

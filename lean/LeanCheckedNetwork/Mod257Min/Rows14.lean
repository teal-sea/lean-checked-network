import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 113 to 120 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_113 : ∀ b, b < 257 →
    (fastOk E1 E2 12 113 b && fastAnswer E1 E2 W2 12 113 b == (113 + b) % 257) = true := by
  decide +kernel

/-- Row 113 of the addition table: the network answers (113 + b) % 257 for every b. -/
theorem row_113 : ∀ b, b < 257 → answer 113 b = (113 + b) % 257 := by
  intro b hb
  have h := fast_113 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 113 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 113 b table_ok h.1, h.2]

theorem fast_114 : ∀ b, b < 257 →
    (fastOk E1 E2 12 114 b && fastAnswer E1 E2 W2 12 114 b == (114 + b) % 257) = true := by
  decide +kernel

/-- Row 114 of the addition table: the network answers (114 + b) % 257 for every b. -/
theorem row_114 : ∀ b, b < 257 → answer 114 b = (114 + b) % 257 := by
  intro b hb
  have h := fast_114 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 114 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 114 b table_ok h.1, h.2]

theorem fast_115 : ∀ b, b < 257 →
    (fastOk E1 E2 12 115 b && fastAnswer E1 E2 W2 12 115 b == (115 + b) % 257) = true := by
  decide +kernel

/-- Row 115 of the addition table: the network answers (115 + b) % 257 for every b. -/
theorem row_115 : ∀ b, b < 257 → answer 115 b = (115 + b) % 257 := by
  intro b hb
  have h := fast_115 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 115 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 115 b table_ok h.1, h.2]

theorem fast_116 : ∀ b, b < 257 →
    (fastOk E1 E2 12 116 b && fastAnswer E1 E2 W2 12 116 b == (116 + b) % 257) = true := by
  decide +kernel

/-- Row 116 of the addition table: the network answers (116 + b) % 257 for every b. -/
theorem row_116 : ∀ b, b < 257 → answer 116 b = (116 + b) % 257 := by
  intro b hb
  have h := fast_116 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 116 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 116 b table_ok h.1, h.2]

theorem fast_117 : ∀ b, b < 257 →
    (fastOk E1 E2 12 117 b && fastAnswer E1 E2 W2 12 117 b == (117 + b) % 257) = true := by
  decide +kernel

/-- Row 117 of the addition table: the network answers (117 + b) % 257 for every b. -/
theorem row_117 : ∀ b, b < 257 → answer 117 b = (117 + b) % 257 := by
  intro b hb
  have h := fast_117 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 117 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 117 b table_ok h.1, h.2]

theorem fast_118 : ∀ b, b < 257 →
    (fastOk E1 E2 12 118 b && fastAnswer E1 E2 W2 12 118 b == (118 + b) % 257) = true := by
  decide +kernel

/-- Row 118 of the addition table: the network answers (118 + b) % 257 for every b. -/
theorem row_118 : ∀ b, b < 257 → answer 118 b = (118 + b) % 257 := by
  intro b hb
  have h := fast_118 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 118 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 118 b table_ok h.1, h.2]

theorem fast_119 : ∀ b, b < 257 →
    (fastOk E1 E2 12 119 b && fastAnswer E1 E2 W2 12 119 b == (119 + b) % 257) = true := by
  decide +kernel

/-- Row 119 of the addition table: the network answers (119 + b) % 257 for every b. -/
theorem row_119 : ∀ b, b < 257 → answer 119 b = (119 + b) % 257 := by
  intro b hb
  have h := fast_119 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 119 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 119 b table_ok h.1, h.2]

theorem fast_120 : ∀ b, b < 257 →
    (fastOk E1 E2 12 120 b && fastAnswer E1 E2 W2 12 120 b == (120 + b) % 257) = true := by
  decide +kernel

/-- Row 120 of the addition table: the network answers (120 + b) % 257 for every b. -/
theorem row_120 : ∀ b, b < 257 → answer 120 b = (120 + b) % 257 := by
  intro b hb
  have h := fast_120 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 120 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 120 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

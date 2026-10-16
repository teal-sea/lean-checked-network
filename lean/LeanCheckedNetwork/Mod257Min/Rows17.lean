import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 137 to 144 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_137 : ∀ b, b < 257 →
    (fastOk E1 E2 12 137 b && fastAnswer E1 E2 W2 12 137 b == (137 + b) % 257) = true := by
  decide +kernel

/-- Row 137 of the addition table: the network answers (137 + b) % 257 for every b. -/
theorem row_137 : ∀ b, b < 257 → answer 137 b = (137 + b) % 257 := by
  intro b hb
  have h := fast_137 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 137 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 137 b table_ok h.1, h.2]

theorem fast_138 : ∀ b, b < 257 →
    (fastOk E1 E2 12 138 b && fastAnswer E1 E2 W2 12 138 b == (138 + b) % 257) = true := by
  decide +kernel

/-- Row 138 of the addition table: the network answers (138 + b) % 257 for every b. -/
theorem row_138 : ∀ b, b < 257 → answer 138 b = (138 + b) % 257 := by
  intro b hb
  have h := fast_138 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 138 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 138 b table_ok h.1, h.2]

theorem fast_139 : ∀ b, b < 257 →
    (fastOk E1 E2 12 139 b && fastAnswer E1 E2 W2 12 139 b == (139 + b) % 257) = true := by
  decide +kernel

/-- Row 139 of the addition table: the network answers (139 + b) % 257 for every b. -/
theorem row_139 : ∀ b, b < 257 → answer 139 b = (139 + b) % 257 := by
  intro b hb
  have h := fast_139 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 139 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 139 b table_ok h.1, h.2]

theorem fast_140 : ∀ b, b < 257 →
    (fastOk E1 E2 12 140 b && fastAnswer E1 E2 W2 12 140 b == (140 + b) % 257) = true := by
  decide +kernel

/-- Row 140 of the addition table: the network answers (140 + b) % 257 for every b. -/
theorem row_140 : ∀ b, b < 257 → answer 140 b = (140 + b) % 257 := by
  intro b hb
  have h := fast_140 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 140 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 140 b table_ok h.1, h.2]

theorem fast_141 : ∀ b, b < 257 →
    (fastOk E1 E2 12 141 b && fastAnswer E1 E2 W2 12 141 b == (141 + b) % 257) = true := by
  decide +kernel

/-- Row 141 of the addition table: the network answers (141 + b) % 257 for every b. -/
theorem row_141 : ∀ b, b < 257 → answer 141 b = (141 + b) % 257 := by
  intro b hb
  have h := fast_141 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 141 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 141 b table_ok h.1, h.2]

theorem fast_142 : ∀ b, b < 257 →
    (fastOk E1 E2 12 142 b && fastAnswer E1 E2 W2 12 142 b == (142 + b) % 257) = true := by
  decide +kernel

/-- Row 142 of the addition table: the network answers (142 + b) % 257 for every b. -/
theorem row_142 : ∀ b, b < 257 → answer 142 b = (142 + b) % 257 := by
  intro b hb
  have h := fast_142 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 142 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 142 b table_ok h.1, h.2]

theorem fast_143 : ∀ b, b < 257 →
    (fastOk E1 E2 12 143 b && fastAnswer E1 E2 W2 12 143 b == (143 + b) % 257) = true := by
  decide +kernel

/-- Row 143 of the addition table: the network answers (143 + b) % 257 for every b. -/
theorem row_143 : ∀ b, b < 257 → answer 143 b = (143 + b) % 257 := by
  intro b hb
  have h := fast_143 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 143 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 143 b table_ok h.1, h.2]

theorem fast_144 : ∀ b, b < 257 →
    (fastOk E1 E2 12 144 b && fastAnswer E1 E2 W2 12 144 b == (144 + b) % 257) = true := by
  decide +kernel

/-- Row 144 of the addition table: the network answers (144 + b) % 257 for every b. -/
theorem row_144 : ∀ b, b < 257 → answer 144 b = (144 + b) % 257 := by
  intro b hb
  have h := fast_144 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 144 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 144 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

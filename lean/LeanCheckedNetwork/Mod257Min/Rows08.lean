import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 129 to 144 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_129 : ∀ b, b < 257 →
    (fastOk E1 E2 12 129 b && fastAnswer E1 E2 W2 12 129 b == (129 + b) % 257) = true := by
  decide +kernel

/-- Row 129 of the addition table: the network answers (129 + b) % 257 for every b. -/
theorem row_129 : ∀ b, b < 257 → answer 129 b = (129 + b) % 257 := by
  intro b hb
  have h := fast_129 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 129 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 129 b table_ok h.1, h.2]

theorem fast_130 : ∀ b, b < 257 →
    (fastOk E1 E2 12 130 b && fastAnswer E1 E2 W2 12 130 b == (130 + b) % 257) = true := by
  decide +kernel

/-- Row 130 of the addition table: the network answers (130 + b) % 257 for every b. -/
theorem row_130 : ∀ b, b < 257 → answer 130 b = (130 + b) % 257 := by
  intro b hb
  have h := fast_130 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 130 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 130 b table_ok h.1, h.2]

theorem fast_131 : ∀ b, b < 257 →
    (fastOk E1 E2 12 131 b && fastAnswer E1 E2 W2 12 131 b == (131 + b) % 257) = true := by
  decide +kernel

/-- Row 131 of the addition table: the network answers (131 + b) % 257 for every b. -/
theorem row_131 : ∀ b, b < 257 → answer 131 b = (131 + b) % 257 := by
  intro b hb
  have h := fast_131 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 131 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 131 b table_ok h.1, h.2]

theorem fast_132 : ∀ b, b < 257 →
    (fastOk E1 E2 12 132 b && fastAnswer E1 E2 W2 12 132 b == (132 + b) % 257) = true := by
  decide +kernel

/-- Row 132 of the addition table: the network answers (132 + b) % 257 for every b. -/
theorem row_132 : ∀ b, b < 257 → answer 132 b = (132 + b) % 257 := by
  intro b hb
  have h := fast_132 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 132 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 132 b table_ok h.1, h.2]

theorem fast_133 : ∀ b, b < 257 →
    (fastOk E1 E2 12 133 b && fastAnswer E1 E2 W2 12 133 b == (133 + b) % 257) = true := by
  decide +kernel

/-- Row 133 of the addition table: the network answers (133 + b) % 257 for every b. -/
theorem row_133 : ∀ b, b < 257 → answer 133 b = (133 + b) % 257 := by
  intro b hb
  have h := fast_133 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 133 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 133 b table_ok h.1, h.2]

theorem fast_134 : ∀ b, b < 257 →
    (fastOk E1 E2 12 134 b && fastAnswer E1 E2 W2 12 134 b == (134 + b) % 257) = true := by
  decide +kernel

/-- Row 134 of the addition table: the network answers (134 + b) % 257 for every b. -/
theorem row_134 : ∀ b, b < 257 → answer 134 b = (134 + b) % 257 := by
  intro b hb
  have h := fast_134 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 134 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 134 b table_ok h.1, h.2]

theorem fast_135 : ∀ b, b < 257 →
    (fastOk E1 E2 12 135 b && fastAnswer E1 E2 W2 12 135 b == (135 + b) % 257) = true := by
  decide +kernel

/-- Row 135 of the addition table: the network answers (135 + b) % 257 for every b. -/
theorem row_135 : ∀ b, b < 257 → answer 135 b = (135 + b) % 257 := by
  intro b hb
  have h := fast_135 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 135 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 135 b table_ok h.1, h.2]

theorem fast_136 : ∀ b, b < 257 →
    (fastOk E1 E2 12 136 b && fastAnswer E1 E2 W2 12 136 b == (136 + b) % 257) = true := by
  decide +kernel

/-- Row 136 of the addition table: the network answers (136 + b) % 257 for every b. -/
theorem row_136 : ∀ b, b < 257 → answer 136 b = (136 + b) % 257 := by
  intro b hb
  have h := fast_136 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 136 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 136 b table_ok h.1, h.2]

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

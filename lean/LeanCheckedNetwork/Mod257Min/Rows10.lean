import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 81 to 88 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_81 : ∀ b, b < 257 →
    (fastOk E1 E2 12 81 b && fastAnswer E1 E2 W2 12 81 b == (81 + b) % 257) = true := by
  decide +kernel

/-- Row 81 of the addition table: the network answers (81 + b) % 257 for every b. -/
theorem row_81 : ∀ b, b < 257 → answer 81 b = (81 + b) % 257 := by
  intro b hb
  have h := fast_81 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 81 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 81 b table_ok h.1, h.2]

theorem fast_82 : ∀ b, b < 257 →
    (fastOk E1 E2 12 82 b && fastAnswer E1 E2 W2 12 82 b == (82 + b) % 257) = true := by
  decide +kernel

/-- Row 82 of the addition table: the network answers (82 + b) % 257 for every b. -/
theorem row_82 : ∀ b, b < 257 → answer 82 b = (82 + b) % 257 := by
  intro b hb
  have h := fast_82 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 82 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 82 b table_ok h.1, h.2]

theorem fast_83 : ∀ b, b < 257 →
    (fastOk E1 E2 12 83 b && fastAnswer E1 E2 W2 12 83 b == (83 + b) % 257) = true := by
  decide +kernel

/-- Row 83 of the addition table: the network answers (83 + b) % 257 for every b. -/
theorem row_83 : ∀ b, b < 257 → answer 83 b = (83 + b) % 257 := by
  intro b hb
  have h := fast_83 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 83 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 83 b table_ok h.1, h.2]

theorem fast_84 : ∀ b, b < 257 →
    (fastOk E1 E2 12 84 b && fastAnswer E1 E2 W2 12 84 b == (84 + b) % 257) = true := by
  decide +kernel

/-- Row 84 of the addition table: the network answers (84 + b) % 257 for every b. -/
theorem row_84 : ∀ b, b < 257 → answer 84 b = (84 + b) % 257 := by
  intro b hb
  have h := fast_84 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 84 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 84 b table_ok h.1, h.2]

theorem fast_85 : ∀ b, b < 257 →
    (fastOk E1 E2 12 85 b && fastAnswer E1 E2 W2 12 85 b == (85 + b) % 257) = true := by
  decide +kernel

/-- Row 85 of the addition table: the network answers (85 + b) % 257 for every b. -/
theorem row_85 : ∀ b, b < 257 → answer 85 b = (85 + b) % 257 := by
  intro b hb
  have h := fast_85 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 85 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 85 b table_ok h.1, h.2]

theorem fast_86 : ∀ b, b < 257 →
    (fastOk E1 E2 12 86 b && fastAnswer E1 E2 W2 12 86 b == (86 + b) % 257) = true := by
  decide +kernel

/-- Row 86 of the addition table: the network answers (86 + b) % 257 for every b. -/
theorem row_86 : ∀ b, b < 257 → answer 86 b = (86 + b) % 257 := by
  intro b hb
  have h := fast_86 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 86 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 86 b table_ok h.1, h.2]

theorem fast_87 : ∀ b, b < 257 →
    (fastOk E1 E2 12 87 b && fastAnswer E1 E2 W2 12 87 b == (87 + b) % 257) = true := by
  decide +kernel

/-- Row 87 of the addition table: the network answers (87 + b) % 257 for every b. -/
theorem row_87 : ∀ b, b < 257 → answer 87 b = (87 + b) % 257 := by
  intro b hb
  have h := fast_87 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 87 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 87 b table_ok h.1, h.2]

theorem fast_88 : ∀ b, b < 257 →
    (fastOk E1 E2 12 88 b && fastAnswer E1 E2 W2 12 88 b == (88 + b) % 257) = true := by
  decide +kernel

/-- Row 88 of the addition table: the network answers (88 + b) % 257 for every b. -/
theorem row_88 : ∀ b, b < 257 → answer 88 b = (88 + b) % 257 := by
  intro b hb
  have h := fast_88 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 88 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 88 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

import LeanCheckedNetwork.FixedPhase16.Table

/-! Rows 85 to 91 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.FixedPhase16

open LeanCheckedNetwork

theorem fast_85 : ∀ b, b < 113 →
    (fastOk E1 E2 16 85 b && fastAnswer E1 E2 W2 16 85 b == (85 + b) % 113) = true := by
  decide +kernel

/-- Row 85 of the addition table: the network answers (85 + b) % 113 for every b. -/
theorem row_85 : ∀ b, b < 113 → answer 85 b = (85 + b) % 113 := by
  intro b hb
  have h := fast_85 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 85 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 16 85 b table_ok h.1, h.2]

theorem fast_86 : ∀ b, b < 113 →
    (fastOk E1 E2 16 86 b && fastAnswer E1 E2 W2 16 86 b == (86 + b) % 113) = true := by
  decide +kernel

/-- Row 86 of the addition table: the network answers (86 + b) % 113 for every b. -/
theorem row_86 : ∀ b, b < 113 → answer 86 b = (86 + b) % 113 := by
  intro b hb
  have h := fast_86 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 86 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 16 86 b table_ok h.1, h.2]

theorem fast_87 : ∀ b, b < 113 →
    (fastOk E1 E2 16 87 b && fastAnswer E1 E2 W2 16 87 b == (87 + b) % 113) = true := by
  decide +kernel

/-- Row 87 of the addition table: the network answers (87 + b) % 113 for every b. -/
theorem row_87 : ∀ b, b < 113 → answer 87 b = (87 + b) % 113 := by
  intro b hb
  have h := fast_87 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 87 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 16 87 b table_ok h.1, h.2]

theorem fast_88 : ∀ b, b < 113 →
    (fastOk E1 E2 16 88 b && fastAnswer E1 E2 W2 16 88 b == (88 + b) % 113) = true := by
  decide +kernel

/-- Row 88 of the addition table: the network answers (88 + b) % 113 for every b. -/
theorem row_88 : ∀ b, b < 113 → answer 88 b = (88 + b) % 113 := by
  intro b hb
  have h := fast_88 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 88 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 16 88 b table_ok h.1, h.2]

theorem fast_89 : ∀ b, b < 113 →
    (fastOk E1 E2 16 89 b && fastAnswer E1 E2 W2 16 89 b == (89 + b) % 113) = true := by
  decide +kernel

/-- Row 89 of the addition table: the network answers (89 + b) % 113 for every b. -/
theorem row_89 : ∀ b, b < 113 → answer 89 b = (89 + b) % 113 := by
  intro b hb
  have h := fast_89 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 89 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 16 89 b table_ok h.1, h.2]

theorem fast_90 : ∀ b, b < 113 →
    (fastOk E1 E2 16 90 b && fastAnswer E1 E2 W2 16 90 b == (90 + b) % 113) = true := by
  decide +kernel

/-- Row 90 of the addition table: the network answers (90 + b) % 113 for every b. -/
theorem row_90 : ∀ b, b < 113 → answer 90 b = (90 + b) % 113 := by
  intro b hb
  have h := fast_90 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 90 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 16 90 b table_ok h.1, h.2]

theorem fast_91 : ∀ b, b < 113 →
    (fastOk E1 E2 16 91 b && fastAnswer E1 E2 W2 16 91 b == (91 + b) % 113) = true := by
  decide +kernel

/-- Row 91 of the addition table: the network answers (91 + b) % 113 for every b. -/
theorem row_91 : ∀ b, b < 113 → answer 91 b = (91 + b) % 113 := by
  intro b hb
  have h := fast_91 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 91 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 16 91 b table_ok h.1, h.2]

end LeanCheckedNetwork.FixedPhase16

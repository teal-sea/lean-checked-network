import LeanCheckedNetwork.FixedPhase40.Table

/-! Rows 92 to 98 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.FixedPhase40

open LeanCheckedNetwork

theorem fast_92 : ∀ b, b < 113 →
    (fastOk E1 E2 40 92 b && fastAnswer E1 E2 W2 40 92 b == (92 + b) % 113) = true := by
  decide +kernel

/-- Row 92 of the addition table: the network answers (92 + b) % 113 for every b. -/
theorem row_92 : ∀ b, b < 113 → answer 92 b = (92 + b) % 113 := by
  intro b hb
  have h := fast_92 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 92 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 92 b table_ok h.1, h.2]

theorem fast_93 : ∀ b, b < 113 →
    (fastOk E1 E2 40 93 b && fastAnswer E1 E2 W2 40 93 b == (93 + b) % 113) = true := by
  decide +kernel

/-- Row 93 of the addition table: the network answers (93 + b) % 113 for every b. -/
theorem row_93 : ∀ b, b < 113 → answer 93 b = (93 + b) % 113 := by
  intro b hb
  have h := fast_93 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 93 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 93 b table_ok h.1, h.2]

theorem fast_94 : ∀ b, b < 113 →
    (fastOk E1 E2 40 94 b && fastAnswer E1 E2 W2 40 94 b == (94 + b) % 113) = true := by
  decide +kernel

/-- Row 94 of the addition table: the network answers (94 + b) % 113 for every b. -/
theorem row_94 : ∀ b, b < 113 → answer 94 b = (94 + b) % 113 := by
  intro b hb
  have h := fast_94 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 94 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 94 b table_ok h.1, h.2]

theorem fast_95 : ∀ b, b < 113 →
    (fastOk E1 E2 40 95 b && fastAnswer E1 E2 W2 40 95 b == (95 + b) % 113) = true := by
  decide +kernel

/-- Row 95 of the addition table: the network answers (95 + b) % 113 for every b. -/
theorem row_95 : ∀ b, b < 113 → answer 95 b = (95 + b) % 113 := by
  intro b hb
  have h := fast_95 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 95 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 95 b table_ok h.1, h.2]

theorem fast_96 : ∀ b, b < 113 →
    (fastOk E1 E2 40 96 b && fastAnswer E1 E2 W2 40 96 b == (96 + b) % 113) = true := by
  decide +kernel

/-- Row 96 of the addition table: the network answers (96 + b) % 113 for every b. -/
theorem row_96 : ∀ b, b < 113 → answer 96 b = (96 + b) % 113 := by
  intro b hb
  have h := fast_96 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 96 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 96 b table_ok h.1, h.2]

theorem fast_97 : ∀ b, b < 113 →
    (fastOk E1 E2 40 97 b && fastAnswer E1 E2 W2 40 97 b == (97 + b) % 113) = true := by
  decide +kernel

/-- Row 97 of the addition table: the network answers (97 + b) % 113 for every b. -/
theorem row_97 : ∀ b, b < 113 → answer 97 b = (97 + b) % 113 := by
  intro b hb
  have h := fast_97 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 97 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 97 b table_ok h.1, h.2]

theorem fast_98 : ∀ b, b < 113 →
    (fastOk E1 E2 40 98 b && fastAnswer E1 E2 W2 40 98 b == (98 + b) % 113) = true := by
  decide +kernel

/-- Row 98 of the addition table: the network answers (98 + b) % 113 for every b. -/
theorem row_98 : ∀ b, b < 113 → answer 98 b = (98 + b) % 113 := by
  intro b hb
  have h := fast_98 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 98 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 98 b table_ok h.1, h.2]

end LeanCheckedNetwork.FixedPhase40

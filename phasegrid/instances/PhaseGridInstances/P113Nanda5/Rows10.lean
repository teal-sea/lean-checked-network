import PhaseGridInstances.P113Nanda5.Table

/-! Rows 71 to 77 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Nanda5

open LeanCheckedNetwork

theorem fast_71 : ∀ b, b < 113 →
    (fastOk E1 E2 40 71 b && fastAnswer E1 E2 W2 40 71 b == (71 + b) % 113) = true := by
  decide +kernel

/-- Row 71 of the addition table: the network answers (71 + b) % 113 for every b. -/
theorem row_71 : ∀ b, b < 113 → answer 71 b = (71 + b) % 113 := by
  intro b hb
  have h := fast_71 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 71 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 71 b table_ok h.1, h.2]

theorem fast_72 : ∀ b, b < 113 →
    (fastOk E1 E2 40 72 b && fastAnswer E1 E2 W2 40 72 b == (72 + b) % 113) = true := by
  decide +kernel

/-- Row 72 of the addition table: the network answers (72 + b) % 113 for every b. -/
theorem row_72 : ∀ b, b < 113 → answer 72 b = (72 + b) % 113 := by
  intro b hb
  have h := fast_72 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 72 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 72 b table_ok h.1, h.2]

theorem fast_73 : ∀ b, b < 113 →
    (fastOk E1 E2 40 73 b && fastAnswer E1 E2 W2 40 73 b == (73 + b) % 113) = true := by
  decide +kernel

/-- Row 73 of the addition table: the network answers (73 + b) % 113 for every b. -/
theorem row_73 : ∀ b, b < 113 → answer 73 b = (73 + b) % 113 := by
  intro b hb
  have h := fast_73 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 73 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 73 b table_ok h.1, h.2]

theorem fast_74 : ∀ b, b < 113 →
    (fastOk E1 E2 40 74 b && fastAnswer E1 E2 W2 40 74 b == (74 + b) % 113) = true := by
  decide +kernel

/-- Row 74 of the addition table: the network answers (74 + b) % 113 for every b. -/
theorem row_74 : ∀ b, b < 113 → answer 74 b = (74 + b) % 113 := by
  intro b hb
  have h := fast_74 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 74 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 74 b table_ok h.1, h.2]

theorem fast_75 : ∀ b, b < 113 →
    (fastOk E1 E2 40 75 b && fastAnswer E1 E2 W2 40 75 b == (75 + b) % 113) = true := by
  decide +kernel

/-- Row 75 of the addition table: the network answers (75 + b) % 113 for every b. -/
theorem row_75 : ∀ b, b < 113 → answer 75 b = (75 + b) % 113 := by
  intro b hb
  have h := fast_75 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 75 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 75 b table_ok h.1, h.2]

theorem fast_76 : ∀ b, b < 113 →
    (fastOk E1 E2 40 76 b && fastAnswer E1 E2 W2 40 76 b == (76 + b) % 113) = true := by
  decide +kernel

/-- Row 76 of the addition table: the network answers (76 + b) % 113 for every b. -/
theorem row_76 : ∀ b, b < 113 → answer 76 b = (76 + b) % 113 := by
  intro b hb
  have h := fast_76 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 76 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 76 b table_ok h.1, h.2]

theorem fast_77 : ∀ b, b < 113 →
    (fastOk E1 E2 40 77 b && fastAnswer E1 E2 W2 40 77 b == (77 + b) % 113) = true := by
  decide +kernel

/-- Row 77 of the addition table: the network answers (77 + b) % 113 for every b. -/
theorem row_77 : ∀ b, b < 113 → answer 77 b = (77 + b) % 113 := by
  intro b hb
  have h := fast_77 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 77 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 40 77 b table_ok h.1, h.2]

end PhaseGridInstances.P113Nanda5

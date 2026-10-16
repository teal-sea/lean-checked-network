import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 105 to 112 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_105 : ∀ b, b < 257 →
    (fastOk E1 E2 12 105 b && fastAnswer E1 E2 W2 12 105 b == (105 + b) % 257) = true := by
  decide +kernel

/-- Row 105 of the addition table: the network answers (105 + b) % 257 for every b. -/
theorem row_105 : ∀ b, b < 257 → answer 105 b = (105 + b) % 257 := by
  intro b hb
  have h := fast_105 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 105 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 105 b table_ok h.1, h.2]

theorem fast_106 : ∀ b, b < 257 →
    (fastOk E1 E2 12 106 b && fastAnswer E1 E2 W2 12 106 b == (106 + b) % 257) = true := by
  decide +kernel

/-- Row 106 of the addition table: the network answers (106 + b) % 257 for every b. -/
theorem row_106 : ∀ b, b < 257 → answer 106 b = (106 + b) % 257 := by
  intro b hb
  have h := fast_106 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 106 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 106 b table_ok h.1, h.2]

theorem fast_107 : ∀ b, b < 257 →
    (fastOk E1 E2 12 107 b && fastAnswer E1 E2 W2 12 107 b == (107 + b) % 257) = true := by
  decide +kernel

/-- Row 107 of the addition table: the network answers (107 + b) % 257 for every b. -/
theorem row_107 : ∀ b, b < 257 → answer 107 b = (107 + b) % 257 := by
  intro b hb
  have h := fast_107 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 107 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 107 b table_ok h.1, h.2]

theorem fast_108 : ∀ b, b < 257 →
    (fastOk E1 E2 12 108 b && fastAnswer E1 E2 W2 12 108 b == (108 + b) % 257) = true := by
  decide +kernel

/-- Row 108 of the addition table: the network answers (108 + b) % 257 for every b. -/
theorem row_108 : ∀ b, b < 257 → answer 108 b = (108 + b) % 257 := by
  intro b hb
  have h := fast_108 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 108 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 108 b table_ok h.1, h.2]

theorem fast_109 : ∀ b, b < 257 →
    (fastOk E1 E2 12 109 b && fastAnswer E1 E2 W2 12 109 b == (109 + b) % 257) = true := by
  decide +kernel

/-- Row 109 of the addition table: the network answers (109 + b) % 257 for every b. -/
theorem row_109 : ∀ b, b < 257 → answer 109 b = (109 + b) % 257 := by
  intro b hb
  have h := fast_109 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 109 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 109 b table_ok h.1, h.2]

theorem fast_110 : ∀ b, b < 257 →
    (fastOk E1 E2 12 110 b && fastAnswer E1 E2 W2 12 110 b == (110 + b) % 257) = true := by
  decide +kernel

/-- Row 110 of the addition table: the network answers (110 + b) % 257 for every b. -/
theorem row_110 : ∀ b, b < 257 → answer 110 b = (110 + b) % 257 := by
  intro b hb
  have h := fast_110 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 110 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 110 b table_ok h.1, h.2]

theorem fast_111 : ∀ b, b < 257 →
    (fastOk E1 E2 12 111 b && fastAnswer E1 E2 W2 12 111 b == (111 + b) % 257) = true := by
  decide +kernel

/-- Row 111 of the addition table: the network answers (111 + b) % 257 for every b. -/
theorem row_111 : ∀ b, b < 257 → answer 111 b = (111 + b) % 257 := by
  intro b hb
  have h := fast_111 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 111 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 111 b table_ok h.1, h.2]

theorem fast_112 : ∀ b, b < 257 →
    (fastOk E1 E2 12 112 b && fastAnswer E1 E2 W2 12 112 b == (112 + b) % 257) = true := by
  decide +kernel

/-- Row 112 of the addition table: the network answers (112 + b) % 257 for every b. -/
theorem row_112 : ∀ b, b < 257 → answer 112 b = (112 + b) % 257 := by
  intro b hb
  have h := fast_112 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 112 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 112 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

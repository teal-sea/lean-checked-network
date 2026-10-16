import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 97 to 104 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_97 : ∀ b, b < 257 →
    (fastOk E1 E2 12 97 b && fastAnswer E1 E2 W2 12 97 b == (97 + b) % 257) = true := by
  decide +kernel

/-- Row 97 of the addition table: the network answers (97 + b) % 257 for every b. -/
theorem row_97 : ∀ b, b < 257 → answer 97 b = (97 + b) % 257 := by
  intro b hb
  have h := fast_97 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 97 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 97 b table_ok h.1, h.2]

theorem fast_98 : ∀ b, b < 257 →
    (fastOk E1 E2 12 98 b && fastAnswer E1 E2 W2 12 98 b == (98 + b) % 257) = true := by
  decide +kernel

/-- Row 98 of the addition table: the network answers (98 + b) % 257 for every b. -/
theorem row_98 : ∀ b, b < 257 → answer 98 b = (98 + b) % 257 := by
  intro b hb
  have h := fast_98 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 98 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 98 b table_ok h.1, h.2]

theorem fast_99 : ∀ b, b < 257 →
    (fastOk E1 E2 12 99 b && fastAnswer E1 E2 W2 12 99 b == (99 + b) % 257) = true := by
  decide +kernel

/-- Row 99 of the addition table: the network answers (99 + b) % 257 for every b. -/
theorem row_99 : ∀ b, b < 257 → answer 99 b = (99 + b) % 257 := by
  intro b hb
  have h := fast_99 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 99 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 99 b table_ok h.1, h.2]

theorem fast_100 : ∀ b, b < 257 →
    (fastOk E1 E2 12 100 b && fastAnswer E1 E2 W2 12 100 b == (100 + b) % 257) = true := by
  decide +kernel

/-- Row 100 of the addition table: the network answers (100 + b) % 257 for every b. -/
theorem row_100 : ∀ b, b < 257 → answer 100 b = (100 + b) % 257 := by
  intro b hb
  have h := fast_100 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 100 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 100 b table_ok h.1, h.2]

theorem fast_101 : ∀ b, b < 257 →
    (fastOk E1 E2 12 101 b && fastAnswer E1 E2 W2 12 101 b == (101 + b) % 257) = true := by
  decide +kernel

/-- Row 101 of the addition table: the network answers (101 + b) % 257 for every b. -/
theorem row_101 : ∀ b, b < 257 → answer 101 b = (101 + b) % 257 := by
  intro b hb
  have h := fast_101 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 101 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 101 b table_ok h.1, h.2]

theorem fast_102 : ∀ b, b < 257 →
    (fastOk E1 E2 12 102 b && fastAnswer E1 E2 W2 12 102 b == (102 + b) % 257) = true := by
  decide +kernel

/-- Row 102 of the addition table: the network answers (102 + b) % 257 for every b. -/
theorem row_102 : ∀ b, b < 257 → answer 102 b = (102 + b) % 257 := by
  intro b hb
  have h := fast_102 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 102 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 102 b table_ok h.1, h.2]

theorem fast_103 : ∀ b, b < 257 →
    (fastOk E1 E2 12 103 b && fastAnswer E1 E2 W2 12 103 b == (103 + b) % 257) = true := by
  decide +kernel

/-- Row 103 of the addition table: the network answers (103 + b) % 257 for every b. -/
theorem row_103 : ∀ b, b < 257 → answer 103 b = (103 + b) % 257 := by
  intro b hb
  have h := fast_103 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 103 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 103 b table_ok h.1, h.2]

theorem fast_104 : ∀ b, b < 257 →
    (fastOk E1 E2 12 104 b && fastAnswer E1 E2 W2 12 104 b == (104 + b) % 257) = true := by
  decide +kernel

/-- Row 104 of the addition table: the network answers (104 + b) % 257 for every b. -/
theorem row_104 : ∀ b, b < 257 → answer 104 b = (104 + b) % 257 := by
  intro b hb
  have h := fast_104 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 104 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 104 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

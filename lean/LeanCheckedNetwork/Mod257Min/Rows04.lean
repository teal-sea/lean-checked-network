import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 33 to 40 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

set_option Elab.async false

namespace LeanCheckedNetwork.Mod257Min

open LeanCheckedNetwork

theorem fast_33 : ∀ b, b < 257 →
    (fastOk E1 E2 12 33 b && fastAnswer E1 E2 W2 12 33 b == (33 + b) % 257) = true := by
  decide +kernel

/-- Row 33 of the addition table: the network answers (33 + b) % 257 for every b. -/
theorem row_33 : ∀ b, b < 257 → answer 33 b = (33 + b) % 257 := by
  intro b hb
  have h := fast_33 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 33 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 33 b table_ok h.1, h.2]

theorem fast_34 : ∀ b, b < 257 →
    (fastOk E1 E2 12 34 b && fastAnswer E1 E2 W2 12 34 b == (34 + b) % 257) = true := by
  decide +kernel

/-- Row 34 of the addition table: the network answers (34 + b) % 257 for every b. -/
theorem row_34 : ∀ b, b < 257 → answer 34 b = (34 + b) % 257 := by
  intro b hb
  have h := fast_34 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 34 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 34 b table_ok h.1, h.2]

theorem fast_35 : ∀ b, b < 257 →
    (fastOk E1 E2 12 35 b && fastAnswer E1 E2 W2 12 35 b == (35 + b) % 257) = true := by
  decide +kernel

/-- Row 35 of the addition table: the network answers (35 + b) % 257 for every b. -/
theorem row_35 : ∀ b, b < 257 → answer 35 b = (35 + b) % 257 := by
  intro b hb
  have h := fast_35 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 35 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 35 b table_ok h.1, h.2]

theorem fast_36 : ∀ b, b < 257 →
    (fastOk E1 E2 12 36 b && fastAnswer E1 E2 W2 12 36 b == (36 + b) % 257) = true := by
  decide +kernel

/-- Row 36 of the addition table: the network answers (36 + b) % 257 for every b. -/
theorem row_36 : ∀ b, b < 257 → answer 36 b = (36 + b) % 257 := by
  intro b hb
  have h := fast_36 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 36 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 36 b table_ok h.1, h.2]

theorem fast_37 : ∀ b, b < 257 →
    (fastOk E1 E2 12 37 b && fastAnswer E1 E2 W2 12 37 b == (37 + b) % 257) = true := by
  decide +kernel

/-- Row 37 of the addition table: the network answers (37 + b) % 257 for every b. -/
theorem row_37 : ∀ b, b < 257 → answer 37 b = (37 + b) % 257 := by
  intro b hb
  have h := fast_37 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 37 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 37 b table_ok h.1, h.2]

theorem fast_38 : ∀ b, b < 257 →
    (fastOk E1 E2 12 38 b && fastAnswer E1 E2 W2 12 38 b == (38 + b) % 257) = true := by
  decide +kernel

/-- Row 38 of the addition table: the network answers (38 + b) % 257 for every b. -/
theorem row_38 : ∀ b, b < 257 → answer 38 b = (38 + b) % 257 := by
  intro b hb
  have h := fast_38 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 38 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 38 b table_ok h.1, h.2]

theorem fast_39 : ∀ b, b < 257 →
    (fastOk E1 E2 12 39 b && fastAnswer E1 E2 W2 12 39 b == (39 + b) % 257) = true := by
  decide +kernel

/-- Row 39 of the addition table: the network answers (39 + b) % 257 for every b. -/
theorem row_39 : ∀ b, b < 257 → answer 39 b = (39 + b) % 257 := by
  intro b hb
  have h := fast_39 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 39 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 39 b table_ok h.1, h.2]

theorem fast_40 : ∀ b, b < 257 →
    (fastOk E1 E2 12 40 b && fastAnswer E1 E2 W2 12 40 b == (40 + b) % 257) = true := by
  decide +kernel

/-- Row 40 of the addition table: the network answers (40 + b) % 257 for every b. -/
theorem row_40 : ∀ b, b < 257 → answer 40 b = (40 + b) % 257 := by
  intro b hb
  have h := fast_40 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  show LeanCheckedNetwork.answer E1 E2 W2 40 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 12 40 b table_ok h.1, h.2]

end LeanCheckedNetwork.Mod257Min

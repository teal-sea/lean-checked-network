import LeanCheckedNetwork.Mod257Min.Table

/-! Rows 97 to 112 of the addition table, checked by Lean's kernel for all 257 values of `b`. -/

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

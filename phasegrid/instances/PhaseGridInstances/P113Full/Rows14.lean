import PhaseGridInstances.P113Full.Table

/-! Rows 99 to 105 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Full

open LeanCheckedNetwork

theorem fast_99_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 99 (0 + b) && fastAnswer E1 E2 W2 448 99 (0 + b) == (99 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_99_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 99 (23 + b) && fastAnswer E1 E2 W2 448 99 (23 + b) == (99 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_99_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 99 (45 + b) && fastAnswer E1 E2 W2 448 99 (45 + b) == (99 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_99_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 99 (68 + b) && fastAnswer E1 E2 W2 448 99 (68 + b) == (99 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_99_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 99 (90 + b) && fastAnswer E1 E2 W2 448 99 (90 + b) == (99 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 99 of the addition table: the network answers (99 + b) % 113 for every b. -/
theorem row_99 : ∀ b, b < 113 → answer 99 b = (99 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 99 b && fastAnswer E1 E2 W2 448 99 b == (99 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_99_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_99_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_99_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_99_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_99_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 99 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 99 b table_ok key.1, key.2]

theorem fast_100_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 100 (0 + b) && fastAnswer E1 E2 W2 448 100 (0 + b) == (100 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_100_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 100 (23 + b) && fastAnswer E1 E2 W2 448 100 (23 + b) == (100 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_100_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 100 (45 + b) && fastAnswer E1 E2 W2 448 100 (45 + b) == (100 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_100_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 100 (68 + b) && fastAnswer E1 E2 W2 448 100 (68 + b) == (100 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_100_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 100 (90 + b) && fastAnswer E1 E2 W2 448 100 (90 + b) == (100 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 100 of the addition table: the network answers (100 + b) % 113 for every b. -/
theorem row_100 : ∀ b, b < 113 → answer 100 b = (100 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 100 b && fastAnswer E1 E2 W2 448 100 b == (100 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_100_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_100_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_100_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_100_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_100_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 100 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 100 b table_ok key.1, key.2]

theorem fast_101_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 101 (0 + b) && fastAnswer E1 E2 W2 448 101 (0 + b) == (101 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_101_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 101 (23 + b) && fastAnswer E1 E2 W2 448 101 (23 + b) == (101 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_101_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 101 (45 + b) && fastAnswer E1 E2 W2 448 101 (45 + b) == (101 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_101_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 101 (68 + b) && fastAnswer E1 E2 W2 448 101 (68 + b) == (101 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_101_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 101 (90 + b) && fastAnswer E1 E2 W2 448 101 (90 + b) == (101 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 101 of the addition table: the network answers (101 + b) % 113 for every b. -/
theorem row_101 : ∀ b, b < 113 → answer 101 b = (101 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 101 b && fastAnswer E1 E2 W2 448 101 b == (101 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_101_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_101_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_101_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_101_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_101_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 101 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 101 b table_ok key.1, key.2]

theorem fast_102_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 102 (0 + b) && fastAnswer E1 E2 W2 448 102 (0 + b) == (102 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_102_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 102 (23 + b) && fastAnswer E1 E2 W2 448 102 (23 + b) == (102 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_102_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 102 (45 + b) && fastAnswer E1 E2 W2 448 102 (45 + b) == (102 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_102_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 102 (68 + b) && fastAnswer E1 E2 W2 448 102 (68 + b) == (102 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_102_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 102 (90 + b) && fastAnswer E1 E2 W2 448 102 (90 + b) == (102 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 102 of the addition table: the network answers (102 + b) % 113 for every b. -/
theorem row_102 : ∀ b, b < 113 → answer 102 b = (102 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 102 b && fastAnswer E1 E2 W2 448 102 b == (102 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_102_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_102_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_102_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_102_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_102_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 102 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 102 b table_ok key.1, key.2]

theorem fast_103_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 103 (0 + b) && fastAnswer E1 E2 W2 448 103 (0 + b) == (103 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_103_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 103 (23 + b) && fastAnswer E1 E2 W2 448 103 (23 + b) == (103 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_103_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 103 (45 + b) && fastAnswer E1 E2 W2 448 103 (45 + b) == (103 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_103_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 103 (68 + b) && fastAnswer E1 E2 W2 448 103 (68 + b) == (103 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_103_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 103 (90 + b) && fastAnswer E1 E2 W2 448 103 (90 + b) == (103 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 103 of the addition table: the network answers (103 + b) % 113 for every b. -/
theorem row_103 : ∀ b, b < 113 → answer 103 b = (103 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 103 b && fastAnswer E1 E2 W2 448 103 b == (103 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_103_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_103_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_103_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_103_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_103_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 103 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 103 b table_ok key.1, key.2]

theorem fast_104_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 104 (0 + b) && fastAnswer E1 E2 W2 448 104 (0 + b) == (104 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_104_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 104 (23 + b) && fastAnswer E1 E2 W2 448 104 (23 + b) == (104 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_104_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 104 (45 + b) && fastAnswer E1 E2 W2 448 104 (45 + b) == (104 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_104_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 104 (68 + b) && fastAnswer E1 E2 W2 448 104 (68 + b) == (104 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_104_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 104 (90 + b) && fastAnswer E1 E2 W2 448 104 (90 + b) == (104 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 104 of the addition table: the network answers (104 + b) % 113 for every b. -/
theorem row_104 : ∀ b, b < 113 → answer 104 b = (104 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 104 b && fastAnswer E1 E2 W2 448 104 b == (104 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_104_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_104_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_104_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_104_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_104_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 104 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 104 b table_ok key.1, key.2]

theorem fast_105_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 105 (0 + b) && fastAnswer E1 E2 W2 448 105 (0 + b) == (105 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_105_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 105 (23 + b) && fastAnswer E1 E2 W2 448 105 (23 + b) == (105 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_105_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 105 (45 + b) && fastAnswer E1 E2 W2 448 105 (45 + b) == (105 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_105_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 105 (68 + b) && fastAnswer E1 E2 W2 448 105 (68 + b) == (105 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_105_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 105 (90 + b) && fastAnswer E1 E2 W2 448 105 (90 + b) == (105 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 105 of the addition table: the network answers (105 + b) % 113 for every b. -/
theorem row_105 : ∀ b, b < 113 → answer 105 b = (105 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 105 b && fastAnswer E1 E2 W2 448 105 b == (105 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_105_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_105_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_105_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_105_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_105_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 105 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 105 b table_ok key.1, key.2]

end PhaseGridInstances.P113Full

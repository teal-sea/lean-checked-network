import PhaseGridInstances.P113Full.Table

/-! Rows 8 to 14 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Full

open LeanCheckedNetwork

theorem fast_8_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 8 (0 + b) && fastAnswer E1 E2 W2 448 8 (0 + b) == (8 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_8_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 8 (23 + b) && fastAnswer E1 E2 W2 448 8 (23 + b) == (8 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_8_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 8 (45 + b) && fastAnswer E1 E2 W2 448 8 (45 + b) == (8 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_8_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 8 (68 + b) && fastAnswer E1 E2 W2 448 8 (68 + b) == (8 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_8_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 8 (90 + b) && fastAnswer E1 E2 W2 448 8 (90 + b) == (8 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 8 of the addition table: the network answers (8 + b) % 113 for every b. -/
theorem row_8 : ∀ b, b < 113 → answer 8 b = (8 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 8 b && fastAnswer E1 E2 W2 448 8 b == (8 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_8_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_8_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_8_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_8_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_8_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 8 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 8 b table_ok key.1, key.2]

theorem fast_9_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 9 (0 + b) && fastAnswer E1 E2 W2 448 9 (0 + b) == (9 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_9_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 9 (23 + b) && fastAnswer E1 E2 W2 448 9 (23 + b) == (9 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_9_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 9 (45 + b) && fastAnswer E1 E2 W2 448 9 (45 + b) == (9 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_9_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 9 (68 + b) && fastAnswer E1 E2 W2 448 9 (68 + b) == (9 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_9_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 9 (90 + b) && fastAnswer E1 E2 W2 448 9 (90 + b) == (9 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 9 of the addition table: the network answers (9 + b) % 113 for every b. -/
theorem row_9 : ∀ b, b < 113 → answer 9 b = (9 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 9 b && fastAnswer E1 E2 W2 448 9 b == (9 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_9_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_9_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_9_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_9_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_9_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 9 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 9 b table_ok key.1, key.2]

theorem fast_10_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 10 (0 + b) && fastAnswer E1 E2 W2 448 10 (0 + b) == (10 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_10_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 10 (23 + b) && fastAnswer E1 E2 W2 448 10 (23 + b) == (10 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_10_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 10 (45 + b) && fastAnswer E1 E2 W2 448 10 (45 + b) == (10 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_10_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 10 (68 + b) && fastAnswer E1 E2 W2 448 10 (68 + b) == (10 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_10_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 10 (90 + b) && fastAnswer E1 E2 W2 448 10 (90 + b) == (10 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 10 of the addition table: the network answers (10 + b) % 113 for every b. -/
theorem row_10 : ∀ b, b < 113 → answer 10 b = (10 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 10 b && fastAnswer E1 E2 W2 448 10 b == (10 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_10_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_10_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_10_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_10_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_10_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 10 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 10 b table_ok key.1, key.2]

theorem fast_11_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 11 (0 + b) && fastAnswer E1 E2 W2 448 11 (0 + b) == (11 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_11_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 11 (23 + b) && fastAnswer E1 E2 W2 448 11 (23 + b) == (11 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_11_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 11 (45 + b) && fastAnswer E1 E2 W2 448 11 (45 + b) == (11 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_11_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 11 (68 + b) && fastAnswer E1 E2 W2 448 11 (68 + b) == (11 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_11_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 11 (90 + b) && fastAnswer E1 E2 W2 448 11 (90 + b) == (11 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 11 of the addition table: the network answers (11 + b) % 113 for every b. -/
theorem row_11 : ∀ b, b < 113 → answer 11 b = (11 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 11 b && fastAnswer E1 E2 W2 448 11 b == (11 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_11_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_11_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_11_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_11_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_11_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 11 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 11 b table_ok key.1, key.2]

theorem fast_12_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 12 (0 + b) && fastAnswer E1 E2 W2 448 12 (0 + b) == (12 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_12_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 12 (23 + b) && fastAnswer E1 E2 W2 448 12 (23 + b) == (12 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_12_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 12 (45 + b) && fastAnswer E1 E2 W2 448 12 (45 + b) == (12 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_12_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 12 (68 + b) && fastAnswer E1 E2 W2 448 12 (68 + b) == (12 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_12_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 12 (90 + b) && fastAnswer E1 E2 W2 448 12 (90 + b) == (12 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 12 of the addition table: the network answers (12 + b) % 113 for every b. -/
theorem row_12 : ∀ b, b < 113 → answer 12 b = (12 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 12 b && fastAnswer E1 E2 W2 448 12 b == (12 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_12_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_12_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_12_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_12_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_12_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 12 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 12 b table_ok key.1, key.2]

theorem fast_13_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 13 (0 + b) && fastAnswer E1 E2 W2 448 13 (0 + b) == (13 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_13_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 13 (23 + b) && fastAnswer E1 E2 W2 448 13 (23 + b) == (13 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_13_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 13 (45 + b) && fastAnswer E1 E2 W2 448 13 (45 + b) == (13 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_13_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 13 (68 + b) && fastAnswer E1 E2 W2 448 13 (68 + b) == (13 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_13_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 13 (90 + b) && fastAnswer E1 E2 W2 448 13 (90 + b) == (13 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 13 of the addition table: the network answers (13 + b) % 113 for every b. -/
theorem row_13 : ∀ b, b < 113 → answer 13 b = (13 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 13 b && fastAnswer E1 E2 W2 448 13 b == (13 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_13_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_13_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_13_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_13_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_13_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 13 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 13 b table_ok key.1, key.2]

theorem fast_14_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 14 (0 + b) && fastAnswer E1 E2 W2 448 14 (0 + b) == (14 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_14_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 14 (23 + b) && fastAnswer E1 E2 W2 448 14 (23 + b) == (14 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_14_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 14 (45 + b) && fastAnswer E1 E2 W2 448 14 (45 + b) == (14 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_14_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 14 (68 + b) && fastAnswer E1 E2 W2 448 14 (68 + b) == (14 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_14_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 14 (90 + b) && fastAnswer E1 E2 W2 448 14 (90 + b) == (14 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 14 of the addition table: the network answers (14 + b) % 113 for every b. -/
theorem row_14 : ∀ b, b < 113 → answer 14 b = (14 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 14 b && fastAnswer E1 E2 W2 448 14 b == (14 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_14_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_14_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_14_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_14_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_14_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 14 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 14 b table_ok key.1, key.2]

end PhaseGridInstances.P113Full

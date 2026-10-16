import PhaseGridInstances.P113Full.Table

/-! Rows 0 to 7 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Full

open LeanCheckedNetwork

theorem fast_0_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 0 (0 + b) && fastAnswer E1 E2 W2 448 0 (0 + b) == (0 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_0_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 0 (23 + b) && fastAnswer E1 E2 W2 448 0 (23 + b) == (0 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_0_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 0 (45 + b) && fastAnswer E1 E2 W2 448 0 (45 + b) == (0 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_0_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 0 (68 + b) && fastAnswer E1 E2 W2 448 0 (68 + b) == (0 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_0_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 0 (90 + b) && fastAnswer E1 E2 W2 448 0 (90 + b) == (0 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 0 of the addition table: the network answers (0 + b) % 113 for every b. -/
theorem row_0 : ∀ b, b < 113 → answer 0 b = (0 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 0 b && fastAnswer E1 E2 W2 448 0 b == (0 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_0_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_0_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_0_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_0_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_0_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 0 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 0 b table_ok key.1, key.2]

theorem fast_1_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 1 (0 + b) && fastAnswer E1 E2 W2 448 1 (0 + b) == (1 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_1_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 1 (23 + b) && fastAnswer E1 E2 W2 448 1 (23 + b) == (1 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_1_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 1 (45 + b) && fastAnswer E1 E2 W2 448 1 (45 + b) == (1 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_1_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 1 (68 + b) && fastAnswer E1 E2 W2 448 1 (68 + b) == (1 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_1_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 1 (90 + b) && fastAnswer E1 E2 W2 448 1 (90 + b) == (1 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 1 of the addition table: the network answers (1 + b) % 113 for every b. -/
theorem row_1 : ∀ b, b < 113 → answer 1 b = (1 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 1 b && fastAnswer E1 E2 W2 448 1 b == (1 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_1_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_1_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_1_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_1_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_1_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 1 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 1 b table_ok key.1, key.2]

theorem fast_2_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 2 (0 + b) && fastAnswer E1 E2 W2 448 2 (0 + b) == (2 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_2_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 2 (23 + b) && fastAnswer E1 E2 W2 448 2 (23 + b) == (2 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_2_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 2 (45 + b) && fastAnswer E1 E2 W2 448 2 (45 + b) == (2 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_2_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 2 (68 + b) && fastAnswer E1 E2 W2 448 2 (68 + b) == (2 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_2_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 2 (90 + b) && fastAnswer E1 E2 W2 448 2 (90 + b) == (2 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 2 of the addition table: the network answers (2 + b) % 113 for every b. -/
theorem row_2 : ∀ b, b < 113 → answer 2 b = (2 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 2 b && fastAnswer E1 E2 W2 448 2 b == (2 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_2_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_2_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_2_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_2_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_2_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 2 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 2 b table_ok key.1, key.2]

theorem fast_3_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 3 (0 + b) && fastAnswer E1 E2 W2 448 3 (0 + b) == (3 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_3_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 3 (23 + b) && fastAnswer E1 E2 W2 448 3 (23 + b) == (3 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_3_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 3 (45 + b) && fastAnswer E1 E2 W2 448 3 (45 + b) == (3 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_3_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 3 (68 + b) && fastAnswer E1 E2 W2 448 3 (68 + b) == (3 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_3_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 3 (90 + b) && fastAnswer E1 E2 W2 448 3 (90 + b) == (3 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 3 of the addition table: the network answers (3 + b) % 113 for every b. -/
theorem row_3 : ∀ b, b < 113 → answer 3 b = (3 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 3 b && fastAnswer E1 E2 W2 448 3 b == (3 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_3_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_3_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_3_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_3_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_3_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 3 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 3 b table_ok key.1, key.2]

theorem fast_4_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 4 (0 + b) && fastAnswer E1 E2 W2 448 4 (0 + b) == (4 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_4_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 4 (23 + b) && fastAnswer E1 E2 W2 448 4 (23 + b) == (4 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_4_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 4 (45 + b) && fastAnswer E1 E2 W2 448 4 (45 + b) == (4 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_4_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 4 (68 + b) && fastAnswer E1 E2 W2 448 4 (68 + b) == (4 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_4_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 4 (90 + b) && fastAnswer E1 E2 W2 448 4 (90 + b) == (4 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 4 of the addition table: the network answers (4 + b) % 113 for every b. -/
theorem row_4 : ∀ b, b < 113 → answer 4 b = (4 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 4 b && fastAnswer E1 E2 W2 448 4 b == (4 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_4_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_4_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_4_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_4_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_4_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 4 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 4 b table_ok key.1, key.2]

theorem fast_5_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 5 (0 + b) && fastAnswer E1 E2 W2 448 5 (0 + b) == (5 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_5_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 5 (23 + b) && fastAnswer E1 E2 W2 448 5 (23 + b) == (5 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_5_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 5 (45 + b) && fastAnswer E1 E2 W2 448 5 (45 + b) == (5 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_5_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 5 (68 + b) && fastAnswer E1 E2 W2 448 5 (68 + b) == (5 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_5_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 5 (90 + b) && fastAnswer E1 E2 W2 448 5 (90 + b) == (5 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 5 of the addition table: the network answers (5 + b) % 113 for every b. -/
theorem row_5 : ∀ b, b < 113 → answer 5 b = (5 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 5 b && fastAnswer E1 E2 W2 448 5 b == (5 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_5_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_5_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_5_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_5_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_5_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 5 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 5 b table_ok key.1, key.2]

theorem fast_6_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 6 (0 + b) && fastAnswer E1 E2 W2 448 6 (0 + b) == (6 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_6_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 6 (23 + b) && fastAnswer E1 E2 W2 448 6 (23 + b) == (6 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_6_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 6 (45 + b) && fastAnswer E1 E2 W2 448 6 (45 + b) == (6 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_6_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 6 (68 + b) && fastAnswer E1 E2 W2 448 6 (68 + b) == (6 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_6_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 6 (90 + b) && fastAnswer E1 E2 W2 448 6 (90 + b) == (6 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 6 of the addition table: the network answers (6 + b) % 113 for every b. -/
theorem row_6 : ∀ b, b < 113 → answer 6 b = (6 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 6 b && fastAnswer E1 E2 W2 448 6 b == (6 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_6_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_6_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_6_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_6_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_6_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 6 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 6 b table_ok key.1, key.2]

theorem fast_7_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 7 (0 + b) && fastAnswer E1 E2 W2 448 7 (0 + b) == (7 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_7_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 7 (23 + b) && fastAnswer E1 E2 W2 448 7 (23 + b) == (7 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_7_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 7 (45 + b) && fastAnswer E1 E2 W2 448 7 (45 + b) == (7 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_7_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 7 (68 + b) && fastAnswer E1 E2 W2 448 7 (68 + b) == (7 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_7_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 7 (90 + b) && fastAnswer E1 E2 W2 448 7 (90 + b) == (7 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 7 of the addition table: the network answers (7 + b) % 113 for every b. -/
theorem row_7 : ∀ b, b < 113 → answer 7 b = (7 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 7 b && fastAnswer E1 E2 W2 448 7 b == (7 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_7_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_7_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_7_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_7_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_7_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 7 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 7 b table_ok key.1, key.2]

end PhaseGridInstances.P113Full

import PhaseGridInstances.P113Full.Table

/-! Rows 22 to 28 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Full

open LeanCheckedNetwork

theorem fast_22_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 22 (0 + b) && fastAnswer E1 E2 W2 448 22 (0 + b) == (22 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_22_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 22 (23 + b) && fastAnswer E1 E2 W2 448 22 (23 + b) == (22 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_22_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 22 (45 + b) && fastAnswer E1 E2 W2 448 22 (45 + b) == (22 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_22_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 22 (68 + b) && fastAnswer E1 E2 W2 448 22 (68 + b) == (22 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_22_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 22 (90 + b) && fastAnswer E1 E2 W2 448 22 (90 + b) == (22 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 22 of the addition table: the network answers (22 + b) % 113 for every b. -/
theorem row_22 : ∀ b, b < 113 → answer 22 b = (22 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 22 b && fastAnswer E1 E2 W2 448 22 b == (22 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_22_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_22_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_22_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_22_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_22_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 22 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 22 b table_ok key.1, key.2]

theorem fast_23_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 23 (0 + b) && fastAnswer E1 E2 W2 448 23 (0 + b) == (23 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_23_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 23 (23 + b) && fastAnswer E1 E2 W2 448 23 (23 + b) == (23 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_23_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 23 (45 + b) && fastAnswer E1 E2 W2 448 23 (45 + b) == (23 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_23_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 23 (68 + b) && fastAnswer E1 E2 W2 448 23 (68 + b) == (23 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_23_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 23 (90 + b) && fastAnswer E1 E2 W2 448 23 (90 + b) == (23 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 23 of the addition table: the network answers (23 + b) % 113 for every b. -/
theorem row_23 : ∀ b, b < 113 → answer 23 b = (23 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 23 b && fastAnswer E1 E2 W2 448 23 b == (23 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_23_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_23_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_23_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_23_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_23_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 23 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 23 b table_ok key.1, key.2]

theorem fast_24_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 24 (0 + b) && fastAnswer E1 E2 W2 448 24 (0 + b) == (24 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_24_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 24 (23 + b) && fastAnswer E1 E2 W2 448 24 (23 + b) == (24 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_24_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 24 (45 + b) && fastAnswer E1 E2 W2 448 24 (45 + b) == (24 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_24_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 24 (68 + b) && fastAnswer E1 E2 W2 448 24 (68 + b) == (24 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_24_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 24 (90 + b) && fastAnswer E1 E2 W2 448 24 (90 + b) == (24 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 24 of the addition table: the network answers (24 + b) % 113 for every b. -/
theorem row_24 : ∀ b, b < 113 → answer 24 b = (24 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 24 b && fastAnswer E1 E2 W2 448 24 b == (24 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_24_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_24_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_24_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_24_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_24_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 24 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 24 b table_ok key.1, key.2]

theorem fast_25_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 25 (0 + b) && fastAnswer E1 E2 W2 448 25 (0 + b) == (25 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_25_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 25 (23 + b) && fastAnswer E1 E2 W2 448 25 (23 + b) == (25 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_25_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 25 (45 + b) && fastAnswer E1 E2 W2 448 25 (45 + b) == (25 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_25_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 25 (68 + b) && fastAnswer E1 E2 W2 448 25 (68 + b) == (25 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_25_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 25 (90 + b) && fastAnswer E1 E2 W2 448 25 (90 + b) == (25 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 25 of the addition table: the network answers (25 + b) % 113 for every b. -/
theorem row_25 : ∀ b, b < 113 → answer 25 b = (25 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 25 b && fastAnswer E1 E2 W2 448 25 b == (25 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_25_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_25_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_25_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_25_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_25_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 25 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 25 b table_ok key.1, key.2]

theorem fast_26_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 26 (0 + b) && fastAnswer E1 E2 W2 448 26 (0 + b) == (26 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_26_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 26 (23 + b) && fastAnswer E1 E2 W2 448 26 (23 + b) == (26 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_26_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 26 (45 + b) && fastAnswer E1 E2 W2 448 26 (45 + b) == (26 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_26_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 26 (68 + b) && fastAnswer E1 E2 W2 448 26 (68 + b) == (26 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_26_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 26 (90 + b) && fastAnswer E1 E2 W2 448 26 (90 + b) == (26 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 26 of the addition table: the network answers (26 + b) % 113 for every b. -/
theorem row_26 : ∀ b, b < 113 → answer 26 b = (26 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 26 b && fastAnswer E1 E2 W2 448 26 b == (26 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_26_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_26_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_26_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_26_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_26_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 26 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 26 b table_ok key.1, key.2]

theorem fast_27_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 27 (0 + b) && fastAnswer E1 E2 W2 448 27 (0 + b) == (27 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_27_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 27 (23 + b) && fastAnswer E1 E2 W2 448 27 (23 + b) == (27 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_27_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 27 (45 + b) && fastAnswer E1 E2 W2 448 27 (45 + b) == (27 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_27_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 27 (68 + b) && fastAnswer E1 E2 W2 448 27 (68 + b) == (27 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_27_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 27 (90 + b) && fastAnswer E1 E2 W2 448 27 (90 + b) == (27 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 27 of the addition table: the network answers (27 + b) % 113 for every b. -/
theorem row_27 : ∀ b, b < 113 → answer 27 b = (27 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 27 b && fastAnswer E1 E2 W2 448 27 b == (27 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_27_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_27_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_27_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_27_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_27_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 27 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 27 b table_ok key.1, key.2]

theorem fast_28_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 28 (0 + b) && fastAnswer E1 E2 W2 448 28 (0 + b) == (28 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_28_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 28 (23 + b) && fastAnswer E1 E2 W2 448 28 (23 + b) == (28 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_28_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 28 (45 + b) && fastAnswer E1 E2 W2 448 28 (45 + b) == (28 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_28_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 28 (68 + b) && fastAnswer E1 E2 W2 448 28 (68 + b) == (28 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_28_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 28 (90 + b) && fastAnswer E1 E2 W2 448 28 (90 + b) == (28 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 28 of the addition table: the network answers (28 + b) % 113 for every b. -/
theorem row_28 : ∀ b, b < 113 → answer 28 b = (28 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 28 b && fastAnswer E1 E2 W2 448 28 b == (28 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_28_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_28_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_28_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_28_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_28_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 28 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 28 b table_ok key.1, key.2]

end PhaseGridInstances.P113Full

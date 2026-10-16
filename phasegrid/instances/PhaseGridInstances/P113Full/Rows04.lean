import PhaseGridInstances.P113Full.Table

/-! Rows 29 to 35 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Full

open LeanCheckedNetwork

theorem fast_29_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 29 (0 + b) && fastAnswer E1 E2 W2 448 29 (0 + b) == (29 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_29_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 29 (23 + b) && fastAnswer E1 E2 W2 448 29 (23 + b) == (29 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_29_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 29 (45 + b) && fastAnswer E1 E2 W2 448 29 (45 + b) == (29 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_29_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 29 (68 + b) && fastAnswer E1 E2 W2 448 29 (68 + b) == (29 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_29_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 29 (90 + b) && fastAnswer E1 E2 W2 448 29 (90 + b) == (29 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 29 of the addition table: the network answers (29 + b) % 113 for every b. -/
theorem row_29 : ∀ b, b < 113 → answer 29 b = (29 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 29 b && fastAnswer E1 E2 W2 448 29 b == (29 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_29_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_29_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_29_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_29_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_29_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 29 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 29 b table_ok key.1, key.2]

theorem fast_30_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 30 (0 + b) && fastAnswer E1 E2 W2 448 30 (0 + b) == (30 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_30_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 30 (23 + b) && fastAnswer E1 E2 W2 448 30 (23 + b) == (30 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_30_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 30 (45 + b) && fastAnswer E1 E2 W2 448 30 (45 + b) == (30 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_30_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 30 (68 + b) && fastAnswer E1 E2 W2 448 30 (68 + b) == (30 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_30_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 30 (90 + b) && fastAnswer E1 E2 W2 448 30 (90 + b) == (30 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 30 of the addition table: the network answers (30 + b) % 113 for every b. -/
theorem row_30 : ∀ b, b < 113 → answer 30 b = (30 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 30 b && fastAnswer E1 E2 W2 448 30 b == (30 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_30_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_30_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_30_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_30_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_30_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 30 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 30 b table_ok key.1, key.2]

theorem fast_31_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 31 (0 + b) && fastAnswer E1 E2 W2 448 31 (0 + b) == (31 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_31_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 31 (23 + b) && fastAnswer E1 E2 W2 448 31 (23 + b) == (31 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_31_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 31 (45 + b) && fastAnswer E1 E2 W2 448 31 (45 + b) == (31 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_31_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 31 (68 + b) && fastAnswer E1 E2 W2 448 31 (68 + b) == (31 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_31_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 31 (90 + b) && fastAnswer E1 E2 W2 448 31 (90 + b) == (31 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 31 of the addition table: the network answers (31 + b) % 113 for every b. -/
theorem row_31 : ∀ b, b < 113 → answer 31 b = (31 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 31 b && fastAnswer E1 E2 W2 448 31 b == (31 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_31_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_31_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_31_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_31_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_31_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 31 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 31 b table_ok key.1, key.2]

theorem fast_32_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 32 (0 + b) && fastAnswer E1 E2 W2 448 32 (0 + b) == (32 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_32_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 32 (23 + b) && fastAnswer E1 E2 W2 448 32 (23 + b) == (32 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_32_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 32 (45 + b) && fastAnswer E1 E2 W2 448 32 (45 + b) == (32 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_32_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 32 (68 + b) && fastAnswer E1 E2 W2 448 32 (68 + b) == (32 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_32_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 32 (90 + b) && fastAnswer E1 E2 W2 448 32 (90 + b) == (32 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 32 of the addition table: the network answers (32 + b) % 113 for every b. -/
theorem row_32 : ∀ b, b < 113 → answer 32 b = (32 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 32 b && fastAnswer E1 E2 W2 448 32 b == (32 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_32_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_32_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_32_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_32_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_32_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 32 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 32 b table_ok key.1, key.2]

theorem fast_33_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 33 (0 + b) && fastAnswer E1 E2 W2 448 33 (0 + b) == (33 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_33_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 33 (23 + b) && fastAnswer E1 E2 W2 448 33 (23 + b) == (33 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_33_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 33 (45 + b) && fastAnswer E1 E2 W2 448 33 (45 + b) == (33 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_33_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 33 (68 + b) && fastAnswer E1 E2 W2 448 33 (68 + b) == (33 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_33_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 33 (90 + b) && fastAnswer E1 E2 W2 448 33 (90 + b) == (33 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 33 of the addition table: the network answers (33 + b) % 113 for every b. -/
theorem row_33 : ∀ b, b < 113 → answer 33 b = (33 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 33 b && fastAnswer E1 E2 W2 448 33 b == (33 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_33_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_33_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_33_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_33_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_33_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 33 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 33 b table_ok key.1, key.2]

theorem fast_34_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 34 (0 + b) && fastAnswer E1 E2 W2 448 34 (0 + b) == (34 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_34_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 34 (23 + b) && fastAnswer E1 E2 W2 448 34 (23 + b) == (34 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_34_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 34 (45 + b) && fastAnswer E1 E2 W2 448 34 (45 + b) == (34 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_34_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 34 (68 + b) && fastAnswer E1 E2 W2 448 34 (68 + b) == (34 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_34_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 34 (90 + b) && fastAnswer E1 E2 W2 448 34 (90 + b) == (34 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 34 of the addition table: the network answers (34 + b) % 113 for every b. -/
theorem row_34 : ∀ b, b < 113 → answer 34 b = (34 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 34 b && fastAnswer E1 E2 W2 448 34 b == (34 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_34_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_34_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_34_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_34_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_34_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 34 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 34 b table_ok key.1, key.2]

theorem fast_35_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 35 (0 + b) && fastAnswer E1 E2 W2 448 35 (0 + b) == (35 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_35_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 35 (23 + b) && fastAnswer E1 E2 W2 448 35 (23 + b) == (35 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_35_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 35 (45 + b) && fastAnswer E1 E2 W2 448 35 (45 + b) == (35 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_35_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 35 (68 + b) && fastAnswer E1 E2 W2 448 35 (68 + b) == (35 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_35_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 35 (90 + b) && fastAnswer E1 E2 W2 448 35 (90 + b) == (35 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 35 of the addition table: the network answers (35 + b) % 113 for every b. -/
theorem row_35 : ∀ b, b < 113 → answer 35 b = (35 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 35 b && fastAnswer E1 E2 W2 448 35 b == (35 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_35_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_35_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_35_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_35_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_35_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 35 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 35 b table_ok key.1, key.2]

end PhaseGridInstances.P113Full

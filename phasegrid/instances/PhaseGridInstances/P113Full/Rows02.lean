import PhaseGridInstances.P113Full.Table

/-! Rows 15 to 21 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Full

open LeanCheckedNetwork

theorem fast_15_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 15 (0 + b) && fastAnswer E1 E2 W2 448 15 (0 + b) == (15 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_15_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 15 (23 + b) && fastAnswer E1 E2 W2 448 15 (23 + b) == (15 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_15_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 15 (45 + b) && fastAnswer E1 E2 W2 448 15 (45 + b) == (15 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_15_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 15 (68 + b) && fastAnswer E1 E2 W2 448 15 (68 + b) == (15 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_15_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 15 (90 + b) && fastAnswer E1 E2 W2 448 15 (90 + b) == (15 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 15 of the addition table: the network answers (15 + b) % 113 for every b. -/
theorem row_15 : ∀ b, b < 113 → answer 15 b = (15 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 15 b && fastAnswer E1 E2 W2 448 15 b == (15 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_15_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_15_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_15_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_15_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_15_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 15 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 15 b table_ok key.1, key.2]

theorem fast_16_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 16 (0 + b) && fastAnswer E1 E2 W2 448 16 (0 + b) == (16 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_16_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 16 (23 + b) && fastAnswer E1 E2 W2 448 16 (23 + b) == (16 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_16_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 16 (45 + b) && fastAnswer E1 E2 W2 448 16 (45 + b) == (16 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_16_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 16 (68 + b) && fastAnswer E1 E2 W2 448 16 (68 + b) == (16 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_16_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 16 (90 + b) && fastAnswer E1 E2 W2 448 16 (90 + b) == (16 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 16 of the addition table: the network answers (16 + b) % 113 for every b. -/
theorem row_16 : ∀ b, b < 113 → answer 16 b = (16 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 16 b && fastAnswer E1 E2 W2 448 16 b == (16 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_16_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_16_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_16_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_16_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_16_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 16 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 16 b table_ok key.1, key.2]

theorem fast_17_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 17 (0 + b) && fastAnswer E1 E2 W2 448 17 (0 + b) == (17 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_17_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 17 (23 + b) && fastAnswer E1 E2 W2 448 17 (23 + b) == (17 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_17_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 17 (45 + b) && fastAnswer E1 E2 W2 448 17 (45 + b) == (17 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_17_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 17 (68 + b) && fastAnswer E1 E2 W2 448 17 (68 + b) == (17 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_17_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 17 (90 + b) && fastAnswer E1 E2 W2 448 17 (90 + b) == (17 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 17 of the addition table: the network answers (17 + b) % 113 for every b. -/
theorem row_17 : ∀ b, b < 113 → answer 17 b = (17 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 17 b && fastAnswer E1 E2 W2 448 17 b == (17 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_17_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_17_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_17_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_17_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_17_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 17 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 17 b table_ok key.1, key.2]

theorem fast_18_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 18 (0 + b) && fastAnswer E1 E2 W2 448 18 (0 + b) == (18 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_18_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 18 (23 + b) && fastAnswer E1 E2 W2 448 18 (23 + b) == (18 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_18_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 18 (45 + b) && fastAnswer E1 E2 W2 448 18 (45 + b) == (18 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_18_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 18 (68 + b) && fastAnswer E1 E2 W2 448 18 (68 + b) == (18 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_18_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 18 (90 + b) && fastAnswer E1 E2 W2 448 18 (90 + b) == (18 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 18 of the addition table: the network answers (18 + b) % 113 for every b. -/
theorem row_18 : ∀ b, b < 113 → answer 18 b = (18 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 18 b && fastAnswer E1 E2 W2 448 18 b == (18 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_18_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_18_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_18_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_18_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_18_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 18 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 18 b table_ok key.1, key.2]

theorem fast_19_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 19 (0 + b) && fastAnswer E1 E2 W2 448 19 (0 + b) == (19 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_19_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 19 (23 + b) && fastAnswer E1 E2 W2 448 19 (23 + b) == (19 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_19_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 19 (45 + b) && fastAnswer E1 E2 W2 448 19 (45 + b) == (19 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_19_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 19 (68 + b) && fastAnswer E1 E2 W2 448 19 (68 + b) == (19 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_19_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 19 (90 + b) && fastAnswer E1 E2 W2 448 19 (90 + b) == (19 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 19 of the addition table: the network answers (19 + b) % 113 for every b. -/
theorem row_19 : ∀ b, b < 113 → answer 19 b = (19 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 19 b && fastAnswer E1 E2 W2 448 19 b == (19 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_19_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_19_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_19_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_19_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_19_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 19 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 19 b table_ok key.1, key.2]

theorem fast_20_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 20 (0 + b) && fastAnswer E1 E2 W2 448 20 (0 + b) == (20 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_20_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 20 (23 + b) && fastAnswer E1 E2 W2 448 20 (23 + b) == (20 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_20_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 20 (45 + b) && fastAnswer E1 E2 W2 448 20 (45 + b) == (20 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_20_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 20 (68 + b) && fastAnswer E1 E2 W2 448 20 (68 + b) == (20 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_20_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 20 (90 + b) && fastAnswer E1 E2 W2 448 20 (90 + b) == (20 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 20 of the addition table: the network answers (20 + b) % 113 for every b. -/
theorem row_20 : ∀ b, b < 113 → answer 20 b = (20 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 20 b && fastAnswer E1 E2 W2 448 20 b == (20 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_20_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_20_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_20_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_20_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_20_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 20 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 20 b table_ok key.1, key.2]

theorem fast_21_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 21 (0 + b) && fastAnswer E1 E2 W2 448 21 (0 + b) == (21 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_21_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 21 (23 + b) && fastAnswer E1 E2 W2 448 21 (23 + b) == (21 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_21_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 21 (45 + b) && fastAnswer E1 E2 W2 448 21 (45 + b) == (21 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_21_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 21 (68 + b) && fastAnswer E1 E2 W2 448 21 (68 + b) == (21 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_21_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 21 (90 + b) && fastAnswer E1 E2 W2 448 21 (90 + b) == (21 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 21 of the addition table: the network answers (21 + b) % 113 for every b. -/
theorem row_21 : ∀ b, b < 113 → answer 21 b = (21 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 21 b && fastAnswer E1 E2 W2 448 21 b == (21 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_21_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_21_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_21_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_21_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_21_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 21 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 21 b table_ok key.1, key.2]

end PhaseGridInstances.P113Full

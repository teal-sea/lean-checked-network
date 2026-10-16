import PhaseGridInstances.P113Full.Table

/-! Rows 36 to 42 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Full

open LeanCheckedNetwork

theorem fast_36_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 36 (0 + b) && fastAnswer E1 E2 W2 448 36 (0 + b) == (36 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_36_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 36 (23 + b) && fastAnswer E1 E2 W2 448 36 (23 + b) == (36 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_36_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 36 (45 + b) && fastAnswer E1 E2 W2 448 36 (45 + b) == (36 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_36_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 36 (68 + b) && fastAnswer E1 E2 W2 448 36 (68 + b) == (36 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_36_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 36 (90 + b) && fastAnswer E1 E2 W2 448 36 (90 + b) == (36 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 36 of the addition table: the network answers (36 + b) % 113 for every b. -/
theorem row_36 : ∀ b, b < 113 → answer 36 b = (36 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 36 b && fastAnswer E1 E2 W2 448 36 b == (36 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_36_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_36_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_36_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_36_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_36_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 36 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 36 b table_ok key.1, key.2]

theorem fast_37_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 37 (0 + b) && fastAnswer E1 E2 W2 448 37 (0 + b) == (37 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_37_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 37 (23 + b) && fastAnswer E1 E2 W2 448 37 (23 + b) == (37 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_37_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 37 (45 + b) && fastAnswer E1 E2 W2 448 37 (45 + b) == (37 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_37_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 37 (68 + b) && fastAnswer E1 E2 W2 448 37 (68 + b) == (37 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_37_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 37 (90 + b) && fastAnswer E1 E2 W2 448 37 (90 + b) == (37 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 37 of the addition table: the network answers (37 + b) % 113 for every b. -/
theorem row_37 : ∀ b, b < 113 → answer 37 b = (37 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 37 b && fastAnswer E1 E2 W2 448 37 b == (37 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_37_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_37_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_37_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_37_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_37_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 37 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 37 b table_ok key.1, key.2]

theorem fast_38_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 38 (0 + b) && fastAnswer E1 E2 W2 448 38 (0 + b) == (38 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_38_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 38 (23 + b) && fastAnswer E1 E2 W2 448 38 (23 + b) == (38 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_38_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 38 (45 + b) && fastAnswer E1 E2 W2 448 38 (45 + b) == (38 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_38_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 38 (68 + b) && fastAnswer E1 E2 W2 448 38 (68 + b) == (38 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_38_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 38 (90 + b) && fastAnswer E1 E2 W2 448 38 (90 + b) == (38 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 38 of the addition table: the network answers (38 + b) % 113 for every b. -/
theorem row_38 : ∀ b, b < 113 → answer 38 b = (38 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 38 b && fastAnswer E1 E2 W2 448 38 b == (38 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_38_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_38_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_38_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_38_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_38_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 38 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 38 b table_ok key.1, key.2]

theorem fast_39_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 39 (0 + b) && fastAnswer E1 E2 W2 448 39 (0 + b) == (39 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_39_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 39 (23 + b) && fastAnswer E1 E2 W2 448 39 (23 + b) == (39 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_39_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 39 (45 + b) && fastAnswer E1 E2 W2 448 39 (45 + b) == (39 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_39_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 39 (68 + b) && fastAnswer E1 E2 W2 448 39 (68 + b) == (39 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_39_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 39 (90 + b) && fastAnswer E1 E2 W2 448 39 (90 + b) == (39 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 39 of the addition table: the network answers (39 + b) % 113 for every b. -/
theorem row_39 : ∀ b, b < 113 → answer 39 b = (39 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 39 b && fastAnswer E1 E2 W2 448 39 b == (39 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_39_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_39_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_39_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_39_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_39_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 39 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 39 b table_ok key.1, key.2]

theorem fast_40_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 40 (0 + b) && fastAnswer E1 E2 W2 448 40 (0 + b) == (40 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_40_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 40 (23 + b) && fastAnswer E1 E2 W2 448 40 (23 + b) == (40 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_40_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 40 (45 + b) && fastAnswer E1 E2 W2 448 40 (45 + b) == (40 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_40_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 40 (68 + b) && fastAnswer E1 E2 W2 448 40 (68 + b) == (40 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_40_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 40 (90 + b) && fastAnswer E1 E2 W2 448 40 (90 + b) == (40 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 40 of the addition table: the network answers (40 + b) % 113 for every b. -/
theorem row_40 : ∀ b, b < 113 → answer 40 b = (40 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 40 b && fastAnswer E1 E2 W2 448 40 b == (40 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_40_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_40_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_40_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_40_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_40_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 40 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 40 b table_ok key.1, key.2]

theorem fast_41_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 41 (0 + b) && fastAnswer E1 E2 W2 448 41 (0 + b) == (41 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_41_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 41 (23 + b) && fastAnswer E1 E2 W2 448 41 (23 + b) == (41 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_41_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 41 (45 + b) && fastAnswer E1 E2 W2 448 41 (45 + b) == (41 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_41_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 41 (68 + b) && fastAnswer E1 E2 W2 448 41 (68 + b) == (41 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_41_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 41 (90 + b) && fastAnswer E1 E2 W2 448 41 (90 + b) == (41 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 41 of the addition table: the network answers (41 + b) % 113 for every b. -/
theorem row_41 : ∀ b, b < 113 → answer 41 b = (41 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 41 b && fastAnswer E1 E2 W2 448 41 b == (41 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_41_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_41_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_41_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_41_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_41_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 41 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 41 b table_ok key.1, key.2]

theorem fast_42_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 42 (0 + b) && fastAnswer E1 E2 W2 448 42 (0 + b) == (42 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_42_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 42 (23 + b) && fastAnswer E1 E2 W2 448 42 (23 + b) == (42 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_42_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 42 (45 + b) && fastAnswer E1 E2 W2 448 42 (45 + b) == (42 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_42_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 42 (68 + b) && fastAnswer E1 E2 W2 448 42 (68 + b) == (42 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_42_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 42 (90 + b) && fastAnswer E1 E2 W2 448 42 (90 + b) == (42 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 42 of the addition table: the network answers (42 + b) % 113 for every b. -/
theorem row_42 : ∀ b, b < 113 → answer 42 b = (42 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 42 b && fastAnswer E1 E2 W2 448 42 b == (42 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_42_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_42_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_42_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_42_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_42_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 42 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 42 b table_ok key.1, key.2]

end PhaseGridInstances.P113Full

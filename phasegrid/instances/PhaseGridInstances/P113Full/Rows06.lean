import PhaseGridInstances.P113Full.Table

/-! Rows 43 to 49 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Full

open LeanCheckedNetwork

theorem fast_43_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 43 (0 + b) && fastAnswer E1 E2 W2 448 43 (0 + b) == (43 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_43_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 43 (23 + b) && fastAnswer E1 E2 W2 448 43 (23 + b) == (43 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_43_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 43 (45 + b) && fastAnswer E1 E2 W2 448 43 (45 + b) == (43 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_43_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 43 (68 + b) && fastAnswer E1 E2 W2 448 43 (68 + b) == (43 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_43_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 43 (90 + b) && fastAnswer E1 E2 W2 448 43 (90 + b) == (43 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 43 of the addition table: the network answers (43 + b) % 113 for every b. -/
theorem row_43 : ∀ b, b < 113 → answer 43 b = (43 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 43 b && fastAnswer E1 E2 W2 448 43 b == (43 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_43_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_43_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_43_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_43_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_43_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 43 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 43 b table_ok key.1, key.2]

theorem fast_44_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 44 (0 + b) && fastAnswer E1 E2 W2 448 44 (0 + b) == (44 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_44_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 44 (23 + b) && fastAnswer E1 E2 W2 448 44 (23 + b) == (44 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_44_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 44 (45 + b) && fastAnswer E1 E2 W2 448 44 (45 + b) == (44 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_44_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 44 (68 + b) && fastAnswer E1 E2 W2 448 44 (68 + b) == (44 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_44_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 44 (90 + b) && fastAnswer E1 E2 W2 448 44 (90 + b) == (44 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 44 of the addition table: the network answers (44 + b) % 113 for every b. -/
theorem row_44 : ∀ b, b < 113 → answer 44 b = (44 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 44 b && fastAnswer E1 E2 W2 448 44 b == (44 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_44_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_44_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_44_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_44_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_44_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 44 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 44 b table_ok key.1, key.2]

theorem fast_45_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 45 (0 + b) && fastAnswer E1 E2 W2 448 45 (0 + b) == (45 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_45_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 45 (23 + b) && fastAnswer E1 E2 W2 448 45 (23 + b) == (45 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_45_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 45 (45 + b) && fastAnswer E1 E2 W2 448 45 (45 + b) == (45 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_45_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 45 (68 + b) && fastAnswer E1 E2 W2 448 45 (68 + b) == (45 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_45_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 45 (90 + b) && fastAnswer E1 E2 W2 448 45 (90 + b) == (45 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 45 of the addition table: the network answers (45 + b) % 113 for every b. -/
theorem row_45 : ∀ b, b < 113 → answer 45 b = (45 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 45 b && fastAnswer E1 E2 W2 448 45 b == (45 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_45_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_45_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_45_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_45_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_45_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 45 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 45 b table_ok key.1, key.2]

theorem fast_46_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 46 (0 + b) && fastAnswer E1 E2 W2 448 46 (0 + b) == (46 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_46_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 46 (23 + b) && fastAnswer E1 E2 W2 448 46 (23 + b) == (46 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_46_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 46 (45 + b) && fastAnswer E1 E2 W2 448 46 (45 + b) == (46 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_46_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 46 (68 + b) && fastAnswer E1 E2 W2 448 46 (68 + b) == (46 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_46_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 46 (90 + b) && fastAnswer E1 E2 W2 448 46 (90 + b) == (46 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 46 of the addition table: the network answers (46 + b) % 113 for every b. -/
theorem row_46 : ∀ b, b < 113 → answer 46 b = (46 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 46 b && fastAnswer E1 E2 W2 448 46 b == (46 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_46_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_46_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_46_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_46_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_46_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 46 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 46 b table_ok key.1, key.2]

theorem fast_47_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 47 (0 + b) && fastAnswer E1 E2 W2 448 47 (0 + b) == (47 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_47_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 47 (23 + b) && fastAnswer E1 E2 W2 448 47 (23 + b) == (47 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_47_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 47 (45 + b) && fastAnswer E1 E2 W2 448 47 (45 + b) == (47 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_47_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 47 (68 + b) && fastAnswer E1 E2 W2 448 47 (68 + b) == (47 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_47_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 47 (90 + b) && fastAnswer E1 E2 W2 448 47 (90 + b) == (47 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 47 of the addition table: the network answers (47 + b) % 113 for every b. -/
theorem row_47 : ∀ b, b < 113 → answer 47 b = (47 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 47 b && fastAnswer E1 E2 W2 448 47 b == (47 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_47_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_47_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_47_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_47_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_47_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 47 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 47 b table_ok key.1, key.2]

theorem fast_48_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 48 (0 + b) && fastAnswer E1 E2 W2 448 48 (0 + b) == (48 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_48_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 48 (23 + b) && fastAnswer E1 E2 W2 448 48 (23 + b) == (48 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_48_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 48 (45 + b) && fastAnswer E1 E2 W2 448 48 (45 + b) == (48 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_48_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 48 (68 + b) && fastAnswer E1 E2 W2 448 48 (68 + b) == (48 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_48_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 48 (90 + b) && fastAnswer E1 E2 W2 448 48 (90 + b) == (48 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 48 of the addition table: the network answers (48 + b) % 113 for every b. -/
theorem row_48 : ∀ b, b < 113 → answer 48 b = (48 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 48 b && fastAnswer E1 E2 W2 448 48 b == (48 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_48_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_48_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_48_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_48_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_48_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 48 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 48 b table_ok key.1, key.2]

theorem fast_49_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 49 (0 + b) && fastAnswer E1 E2 W2 448 49 (0 + b) == (49 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_49_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 49 (23 + b) && fastAnswer E1 E2 W2 448 49 (23 + b) == (49 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_49_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 49 (45 + b) && fastAnswer E1 E2 W2 448 49 (45 + b) == (49 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_49_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 49 (68 + b) && fastAnswer E1 E2 W2 448 49 (68 + b) == (49 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_49_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 49 (90 + b) && fastAnswer E1 E2 W2 448 49 (90 + b) == (49 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 49 of the addition table: the network answers (49 + b) % 113 for every b. -/
theorem row_49 : ∀ b, b < 113 → answer 49 b = (49 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 49 b && fastAnswer E1 E2 W2 448 49 b == (49 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_49_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_49_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_49_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_49_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_49_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 49 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 49 b table_ok key.1, key.2]

end PhaseGridInstances.P113Full

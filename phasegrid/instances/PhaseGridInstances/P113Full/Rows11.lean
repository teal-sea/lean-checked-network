import PhaseGridInstances.P113Full.Table

/-! Rows 78 to 84 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Full

open LeanCheckedNetwork

theorem fast_78_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 78 (0 + b) && fastAnswer E1 E2 W2 448 78 (0 + b) == (78 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_78_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 78 (23 + b) && fastAnswer E1 E2 W2 448 78 (23 + b) == (78 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_78_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 78 (45 + b) && fastAnswer E1 E2 W2 448 78 (45 + b) == (78 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_78_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 78 (68 + b) && fastAnswer E1 E2 W2 448 78 (68 + b) == (78 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_78_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 78 (90 + b) && fastAnswer E1 E2 W2 448 78 (90 + b) == (78 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 78 of the addition table: the network answers (78 + b) % 113 for every b. -/
theorem row_78 : ∀ b, b < 113 → answer 78 b = (78 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 78 b && fastAnswer E1 E2 W2 448 78 b == (78 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_78_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_78_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_78_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_78_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_78_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 78 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 78 b table_ok key.1, key.2]

theorem fast_79_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 79 (0 + b) && fastAnswer E1 E2 W2 448 79 (0 + b) == (79 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_79_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 79 (23 + b) && fastAnswer E1 E2 W2 448 79 (23 + b) == (79 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_79_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 79 (45 + b) && fastAnswer E1 E2 W2 448 79 (45 + b) == (79 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_79_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 79 (68 + b) && fastAnswer E1 E2 W2 448 79 (68 + b) == (79 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_79_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 79 (90 + b) && fastAnswer E1 E2 W2 448 79 (90 + b) == (79 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 79 of the addition table: the network answers (79 + b) % 113 for every b. -/
theorem row_79 : ∀ b, b < 113 → answer 79 b = (79 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 79 b && fastAnswer E1 E2 W2 448 79 b == (79 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_79_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_79_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_79_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_79_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_79_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 79 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 79 b table_ok key.1, key.2]

theorem fast_80_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 80 (0 + b) && fastAnswer E1 E2 W2 448 80 (0 + b) == (80 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_80_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 80 (23 + b) && fastAnswer E1 E2 W2 448 80 (23 + b) == (80 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_80_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 80 (45 + b) && fastAnswer E1 E2 W2 448 80 (45 + b) == (80 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_80_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 80 (68 + b) && fastAnswer E1 E2 W2 448 80 (68 + b) == (80 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_80_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 80 (90 + b) && fastAnswer E1 E2 W2 448 80 (90 + b) == (80 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 80 of the addition table: the network answers (80 + b) % 113 for every b. -/
theorem row_80 : ∀ b, b < 113 → answer 80 b = (80 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 80 b && fastAnswer E1 E2 W2 448 80 b == (80 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_80_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_80_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_80_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_80_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_80_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 80 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 80 b table_ok key.1, key.2]

theorem fast_81_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 81 (0 + b) && fastAnswer E1 E2 W2 448 81 (0 + b) == (81 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_81_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 81 (23 + b) && fastAnswer E1 E2 W2 448 81 (23 + b) == (81 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_81_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 81 (45 + b) && fastAnswer E1 E2 W2 448 81 (45 + b) == (81 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_81_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 81 (68 + b) && fastAnswer E1 E2 W2 448 81 (68 + b) == (81 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_81_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 81 (90 + b) && fastAnswer E1 E2 W2 448 81 (90 + b) == (81 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 81 of the addition table: the network answers (81 + b) % 113 for every b. -/
theorem row_81 : ∀ b, b < 113 → answer 81 b = (81 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 81 b && fastAnswer E1 E2 W2 448 81 b == (81 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_81_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_81_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_81_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_81_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_81_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 81 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 81 b table_ok key.1, key.2]

theorem fast_82_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 82 (0 + b) && fastAnswer E1 E2 W2 448 82 (0 + b) == (82 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_82_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 82 (23 + b) && fastAnswer E1 E2 W2 448 82 (23 + b) == (82 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_82_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 82 (45 + b) && fastAnswer E1 E2 W2 448 82 (45 + b) == (82 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_82_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 82 (68 + b) && fastAnswer E1 E2 W2 448 82 (68 + b) == (82 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_82_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 82 (90 + b) && fastAnswer E1 E2 W2 448 82 (90 + b) == (82 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 82 of the addition table: the network answers (82 + b) % 113 for every b. -/
theorem row_82 : ∀ b, b < 113 → answer 82 b = (82 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 82 b && fastAnswer E1 E2 W2 448 82 b == (82 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_82_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_82_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_82_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_82_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_82_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 82 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 82 b table_ok key.1, key.2]

theorem fast_83_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 83 (0 + b) && fastAnswer E1 E2 W2 448 83 (0 + b) == (83 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_83_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 83 (23 + b) && fastAnswer E1 E2 W2 448 83 (23 + b) == (83 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_83_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 83 (45 + b) && fastAnswer E1 E2 W2 448 83 (45 + b) == (83 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_83_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 83 (68 + b) && fastAnswer E1 E2 W2 448 83 (68 + b) == (83 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_83_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 83 (90 + b) && fastAnswer E1 E2 W2 448 83 (90 + b) == (83 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 83 of the addition table: the network answers (83 + b) % 113 for every b. -/
theorem row_83 : ∀ b, b < 113 → answer 83 b = (83 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 83 b && fastAnswer E1 E2 W2 448 83 b == (83 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_83_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_83_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_83_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_83_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_83_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 83 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 83 b table_ok key.1, key.2]

theorem fast_84_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 84 (0 + b) && fastAnswer E1 E2 W2 448 84 (0 + b) == (84 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_84_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 84 (23 + b) && fastAnswer E1 E2 W2 448 84 (23 + b) == (84 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_84_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 84 (45 + b) && fastAnswer E1 E2 W2 448 84 (45 + b) == (84 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_84_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 84 (68 + b) && fastAnswer E1 E2 W2 448 84 (68 + b) == (84 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_84_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 84 (90 + b) && fastAnswer E1 E2 W2 448 84 (90 + b) == (84 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 84 of the addition table: the network answers (84 + b) % 113 for every b. -/
theorem row_84 : ∀ b, b < 113 → answer 84 b = (84 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 84 b && fastAnswer E1 E2 W2 448 84 b == (84 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_84_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_84_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_84_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_84_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_84_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 84 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 84 b table_ok key.1, key.2]

end PhaseGridInstances.P113Full

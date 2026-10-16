import PhaseGridInstances.P113Full.Table

/-! Rows 64 to 70 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Full

open LeanCheckedNetwork

theorem fast_64_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 64 (0 + b) && fastAnswer E1 E2 W2 448 64 (0 + b) == (64 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_64_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 64 (23 + b) && fastAnswer E1 E2 W2 448 64 (23 + b) == (64 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_64_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 64 (45 + b) && fastAnswer E1 E2 W2 448 64 (45 + b) == (64 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_64_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 64 (68 + b) && fastAnswer E1 E2 W2 448 64 (68 + b) == (64 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_64_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 64 (90 + b) && fastAnswer E1 E2 W2 448 64 (90 + b) == (64 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 64 of the addition table: the network answers (64 + b) % 113 for every b. -/
theorem row_64 : ∀ b, b < 113 → answer 64 b = (64 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 64 b && fastAnswer E1 E2 W2 448 64 b == (64 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_64_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_64_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_64_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_64_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_64_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 64 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 64 b table_ok key.1, key.2]

theorem fast_65_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 65 (0 + b) && fastAnswer E1 E2 W2 448 65 (0 + b) == (65 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_65_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 65 (23 + b) && fastAnswer E1 E2 W2 448 65 (23 + b) == (65 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_65_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 65 (45 + b) && fastAnswer E1 E2 W2 448 65 (45 + b) == (65 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_65_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 65 (68 + b) && fastAnswer E1 E2 W2 448 65 (68 + b) == (65 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_65_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 65 (90 + b) && fastAnswer E1 E2 W2 448 65 (90 + b) == (65 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 65 of the addition table: the network answers (65 + b) % 113 for every b. -/
theorem row_65 : ∀ b, b < 113 → answer 65 b = (65 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 65 b && fastAnswer E1 E2 W2 448 65 b == (65 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_65_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_65_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_65_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_65_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_65_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 65 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 65 b table_ok key.1, key.2]

theorem fast_66_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 66 (0 + b) && fastAnswer E1 E2 W2 448 66 (0 + b) == (66 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_66_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 66 (23 + b) && fastAnswer E1 E2 W2 448 66 (23 + b) == (66 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_66_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 66 (45 + b) && fastAnswer E1 E2 W2 448 66 (45 + b) == (66 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_66_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 66 (68 + b) && fastAnswer E1 E2 W2 448 66 (68 + b) == (66 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_66_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 66 (90 + b) && fastAnswer E1 E2 W2 448 66 (90 + b) == (66 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 66 of the addition table: the network answers (66 + b) % 113 for every b. -/
theorem row_66 : ∀ b, b < 113 → answer 66 b = (66 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 66 b && fastAnswer E1 E2 W2 448 66 b == (66 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_66_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_66_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_66_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_66_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_66_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 66 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 66 b table_ok key.1, key.2]

theorem fast_67_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 67 (0 + b) && fastAnswer E1 E2 W2 448 67 (0 + b) == (67 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_67_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 67 (23 + b) && fastAnswer E1 E2 W2 448 67 (23 + b) == (67 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_67_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 67 (45 + b) && fastAnswer E1 E2 W2 448 67 (45 + b) == (67 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_67_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 67 (68 + b) && fastAnswer E1 E2 W2 448 67 (68 + b) == (67 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_67_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 67 (90 + b) && fastAnswer E1 E2 W2 448 67 (90 + b) == (67 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 67 of the addition table: the network answers (67 + b) % 113 for every b. -/
theorem row_67 : ∀ b, b < 113 → answer 67 b = (67 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 67 b && fastAnswer E1 E2 W2 448 67 b == (67 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_67_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_67_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_67_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_67_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_67_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 67 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 67 b table_ok key.1, key.2]

theorem fast_68_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 68 (0 + b) && fastAnswer E1 E2 W2 448 68 (0 + b) == (68 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_68_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 68 (23 + b) && fastAnswer E1 E2 W2 448 68 (23 + b) == (68 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_68_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 68 (45 + b) && fastAnswer E1 E2 W2 448 68 (45 + b) == (68 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_68_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 68 (68 + b) && fastAnswer E1 E2 W2 448 68 (68 + b) == (68 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_68_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 68 (90 + b) && fastAnswer E1 E2 W2 448 68 (90 + b) == (68 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 68 of the addition table: the network answers (68 + b) % 113 for every b. -/
theorem row_68 : ∀ b, b < 113 → answer 68 b = (68 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 68 b && fastAnswer E1 E2 W2 448 68 b == (68 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_68_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_68_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_68_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_68_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_68_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 68 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 68 b table_ok key.1, key.2]

theorem fast_69_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 69 (0 + b) && fastAnswer E1 E2 W2 448 69 (0 + b) == (69 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_69_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 69 (23 + b) && fastAnswer E1 E2 W2 448 69 (23 + b) == (69 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_69_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 69 (45 + b) && fastAnswer E1 E2 W2 448 69 (45 + b) == (69 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_69_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 69 (68 + b) && fastAnswer E1 E2 W2 448 69 (68 + b) == (69 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_69_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 69 (90 + b) && fastAnswer E1 E2 W2 448 69 (90 + b) == (69 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 69 of the addition table: the network answers (69 + b) % 113 for every b. -/
theorem row_69 : ∀ b, b < 113 → answer 69 b = (69 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 69 b && fastAnswer E1 E2 W2 448 69 b == (69 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_69_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_69_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_69_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_69_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_69_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 69 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 69 b table_ok key.1, key.2]

theorem fast_70_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 70 (0 + b) && fastAnswer E1 E2 W2 448 70 (0 + b) == (70 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_70_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 70 (23 + b) && fastAnswer E1 E2 W2 448 70 (23 + b) == (70 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_70_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 70 (45 + b) && fastAnswer E1 E2 W2 448 70 (45 + b) == (70 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_70_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 70 (68 + b) && fastAnswer E1 E2 W2 448 70 (68 + b) == (70 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_70_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 70 (90 + b) && fastAnswer E1 E2 W2 448 70 (90 + b) == (70 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 70 of the addition table: the network answers (70 + b) % 113 for every b. -/
theorem row_70 : ∀ b, b < 113 → answer 70 b = (70 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 70 b && fastAnswer E1 E2 W2 448 70 b == (70 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_70_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_70_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_70_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_70_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_70_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 70 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 70 b table_ok key.1, key.2]

end PhaseGridInstances.P113Full

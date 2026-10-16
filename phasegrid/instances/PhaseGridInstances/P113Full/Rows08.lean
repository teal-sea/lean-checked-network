import PhaseGridInstances.P113Full.Table

/-! Rows 57 to 63 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Full

open LeanCheckedNetwork

theorem fast_57_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 57 (0 + b) && fastAnswer E1 E2 W2 448 57 (0 + b) == (57 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_57_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 57 (23 + b) && fastAnswer E1 E2 W2 448 57 (23 + b) == (57 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_57_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 57 (45 + b) && fastAnswer E1 E2 W2 448 57 (45 + b) == (57 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_57_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 57 (68 + b) && fastAnswer E1 E2 W2 448 57 (68 + b) == (57 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_57_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 57 (90 + b) && fastAnswer E1 E2 W2 448 57 (90 + b) == (57 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 57 of the addition table: the network answers (57 + b) % 113 for every b. -/
theorem row_57 : ∀ b, b < 113 → answer 57 b = (57 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 57 b && fastAnswer E1 E2 W2 448 57 b == (57 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_57_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_57_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_57_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_57_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_57_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 57 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 57 b table_ok key.1, key.2]

theorem fast_58_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 58 (0 + b) && fastAnswer E1 E2 W2 448 58 (0 + b) == (58 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_58_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 58 (23 + b) && fastAnswer E1 E2 W2 448 58 (23 + b) == (58 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_58_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 58 (45 + b) && fastAnswer E1 E2 W2 448 58 (45 + b) == (58 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_58_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 58 (68 + b) && fastAnswer E1 E2 W2 448 58 (68 + b) == (58 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_58_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 58 (90 + b) && fastAnswer E1 E2 W2 448 58 (90 + b) == (58 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 58 of the addition table: the network answers (58 + b) % 113 for every b. -/
theorem row_58 : ∀ b, b < 113 → answer 58 b = (58 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 58 b && fastAnswer E1 E2 W2 448 58 b == (58 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_58_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_58_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_58_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_58_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_58_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 58 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 58 b table_ok key.1, key.2]

theorem fast_59_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 59 (0 + b) && fastAnswer E1 E2 W2 448 59 (0 + b) == (59 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_59_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 59 (23 + b) && fastAnswer E1 E2 W2 448 59 (23 + b) == (59 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_59_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 59 (45 + b) && fastAnswer E1 E2 W2 448 59 (45 + b) == (59 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_59_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 59 (68 + b) && fastAnswer E1 E2 W2 448 59 (68 + b) == (59 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_59_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 59 (90 + b) && fastAnswer E1 E2 W2 448 59 (90 + b) == (59 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 59 of the addition table: the network answers (59 + b) % 113 for every b. -/
theorem row_59 : ∀ b, b < 113 → answer 59 b = (59 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 59 b && fastAnswer E1 E2 W2 448 59 b == (59 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_59_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_59_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_59_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_59_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_59_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 59 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 59 b table_ok key.1, key.2]

theorem fast_60_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 60 (0 + b) && fastAnswer E1 E2 W2 448 60 (0 + b) == (60 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_60_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 60 (23 + b) && fastAnswer E1 E2 W2 448 60 (23 + b) == (60 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_60_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 60 (45 + b) && fastAnswer E1 E2 W2 448 60 (45 + b) == (60 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_60_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 60 (68 + b) && fastAnswer E1 E2 W2 448 60 (68 + b) == (60 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_60_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 60 (90 + b) && fastAnswer E1 E2 W2 448 60 (90 + b) == (60 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 60 of the addition table: the network answers (60 + b) % 113 for every b. -/
theorem row_60 : ∀ b, b < 113 → answer 60 b = (60 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 60 b && fastAnswer E1 E2 W2 448 60 b == (60 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_60_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_60_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_60_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_60_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_60_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 60 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 60 b table_ok key.1, key.2]

theorem fast_61_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 61 (0 + b) && fastAnswer E1 E2 W2 448 61 (0 + b) == (61 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_61_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 61 (23 + b) && fastAnswer E1 E2 W2 448 61 (23 + b) == (61 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_61_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 61 (45 + b) && fastAnswer E1 E2 W2 448 61 (45 + b) == (61 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_61_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 61 (68 + b) && fastAnswer E1 E2 W2 448 61 (68 + b) == (61 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_61_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 61 (90 + b) && fastAnswer E1 E2 W2 448 61 (90 + b) == (61 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 61 of the addition table: the network answers (61 + b) % 113 for every b. -/
theorem row_61 : ∀ b, b < 113 → answer 61 b = (61 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 61 b && fastAnswer E1 E2 W2 448 61 b == (61 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_61_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_61_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_61_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_61_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_61_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 61 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 61 b table_ok key.1, key.2]

theorem fast_62_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 62 (0 + b) && fastAnswer E1 E2 W2 448 62 (0 + b) == (62 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_62_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 62 (23 + b) && fastAnswer E1 E2 W2 448 62 (23 + b) == (62 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_62_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 62 (45 + b) && fastAnswer E1 E2 W2 448 62 (45 + b) == (62 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_62_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 62 (68 + b) && fastAnswer E1 E2 W2 448 62 (68 + b) == (62 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_62_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 62 (90 + b) && fastAnswer E1 E2 W2 448 62 (90 + b) == (62 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 62 of the addition table: the network answers (62 + b) % 113 for every b. -/
theorem row_62 : ∀ b, b < 113 → answer 62 b = (62 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 62 b && fastAnswer E1 E2 W2 448 62 b == (62 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_62_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_62_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_62_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_62_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_62_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 62 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 62 b table_ok key.1, key.2]

theorem fast_63_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 63 (0 + b) && fastAnswer E1 E2 W2 448 63 (0 + b) == (63 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_63_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 63 (23 + b) && fastAnswer E1 E2 W2 448 63 (23 + b) == (63 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_63_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 63 (45 + b) && fastAnswer E1 E2 W2 448 63 (45 + b) == (63 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_63_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 63 (68 + b) && fastAnswer E1 E2 W2 448 63 (68 + b) == (63 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_63_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 63 (90 + b) && fastAnswer E1 E2 W2 448 63 (90 + b) == (63 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 63 of the addition table: the network answers (63 + b) % 113 for every b. -/
theorem row_63 : ∀ b, b < 113 → answer 63 b = (63 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 63 b && fastAnswer E1 E2 W2 448 63 b == (63 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_63_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_63_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_63_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_63_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_63_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 63 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 63 b table_ok key.1, key.2]

end PhaseGridInstances.P113Full

import PhaseGridInstances.P113Full.Table

/-! Rows 92 to 98 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Full

open LeanCheckedNetwork

theorem fast_92_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 92 (0 + b) && fastAnswer E1 E2 W2 448 92 (0 + b) == (92 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_92_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 92 (23 + b) && fastAnswer E1 E2 W2 448 92 (23 + b) == (92 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_92_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 92 (45 + b) && fastAnswer E1 E2 W2 448 92 (45 + b) == (92 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_92_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 92 (68 + b) && fastAnswer E1 E2 W2 448 92 (68 + b) == (92 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_92_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 92 (90 + b) && fastAnswer E1 E2 W2 448 92 (90 + b) == (92 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 92 of the addition table: the network answers (92 + b) % 113 for every b. -/
theorem row_92 : ∀ b, b < 113 → answer 92 b = (92 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 92 b && fastAnswer E1 E2 W2 448 92 b == (92 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_92_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_92_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_92_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_92_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_92_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 92 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 92 b table_ok key.1, key.2]

theorem fast_93_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 93 (0 + b) && fastAnswer E1 E2 W2 448 93 (0 + b) == (93 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_93_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 93 (23 + b) && fastAnswer E1 E2 W2 448 93 (23 + b) == (93 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_93_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 93 (45 + b) && fastAnswer E1 E2 W2 448 93 (45 + b) == (93 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_93_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 93 (68 + b) && fastAnswer E1 E2 W2 448 93 (68 + b) == (93 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_93_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 93 (90 + b) && fastAnswer E1 E2 W2 448 93 (90 + b) == (93 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 93 of the addition table: the network answers (93 + b) % 113 for every b. -/
theorem row_93 : ∀ b, b < 113 → answer 93 b = (93 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 93 b && fastAnswer E1 E2 W2 448 93 b == (93 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_93_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_93_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_93_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_93_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_93_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 93 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 93 b table_ok key.1, key.2]

theorem fast_94_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 94 (0 + b) && fastAnswer E1 E2 W2 448 94 (0 + b) == (94 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_94_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 94 (23 + b) && fastAnswer E1 E2 W2 448 94 (23 + b) == (94 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_94_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 94 (45 + b) && fastAnswer E1 E2 W2 448 94 (45 + b) == (94 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_94_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 94 (68 + b) && fastAnswer E1 E2 W2 448 94 (68 + b) == (94 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_94_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 94 (90 + b) && fastAnswer E1 E2 W2 448 94 (90 + b) == (94 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 94 of the addition table: the network answers (94 + b) % 113 for every b. -/
theorem row_94 : ∀ b, b < 113 → answer 94 b = (94 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 94 b && fastAnswer E1 E2 W2 448 94 b == (94 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_94_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_94_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_94_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_94_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_94_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 94 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 94 b table_ok key.1, key.2]

theorem fast_95_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 95 (0 + b) && fastAnswer E1 E2 W2 448 95 (0 + b) == (95 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_95_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 95 (23 + b) && fastAnswer E1 E2 W2 448 95 (23 + b) == (95 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_95_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 95 (45 + b) && fastAnswer E1 E2 W2 448 95 (45 + b) == (95 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_95_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 95 (68 + b) && fastAnswer E1 E2 W2 448 95 (68 + b) == (95 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_95_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 95 (90 + b) && fastAnswer E1 E2 W2 448 95 (90 + b) == (95 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 95 of the addition table: the network answers (95 + b) % 113 for every b. -/
theorem row_95 : ∀ b, b < 113 → answer 95 b = (95 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 95 b && fastAnswer E1 E2 W2 448 95 b == (95 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_95_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_95_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_95_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_95_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_95_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 95 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 95 b table_ok key.1, key.2]

theorem fast_96_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 96 (0 + b) && fastAnswer E1 E2 W2 448 96 (0 + b) == (96 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_96_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 96 (23 + b) && fastAnswer E1 E2 W2 448 96 (23 + b) == (96 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_96_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 96 (45 + b) && fastAnswer E1 E2 W2 448 96 (45 + b) == (96 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_96_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 96 (68 + b) && fastAnswer E1 E2 W2 448 96 (68 + b) == (96 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_96_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 96 (90 + b) && fastAnswer E1 E2 W2 448 96 (90 + b) == (96 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 96 of the addition table: the network answers (96 + b) % 113 for every b. -/
theorem row_96 : ∀ b, b < 113 → answer 96 b = (96 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 96 b && fastAnswer E1 E2 W2 448 96 b == (96 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_96_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_96_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_96_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_96_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_96_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 96 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 96 b table_ok key.1, key.2]

theorem fast_97_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 97 (0 + b) && fastAnswer E1 E2 W2 448 97 (0 + b) == (97 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_97_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 97 (23 + b) && fastAnswer E1 E2 W2 448 97 (23 + b) == (97 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_97_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 97 (45 + b) && fastAnswer E1 E2 W2 448 97 (45 + b) == (97 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_97_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 97 (68 + b) && fastAnswer E1 E2 W2 448 97 (68 + b) == (97 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_97_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 97 (90 + b) && fastAnswer E1 E2 W2 448 97 (90 + b) == (97 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 97 of the addition table: the network answers (97 + b) % 113 for every b. -/
theorem row_97 : ∀ b, b < 113 → answer 97 b = (97 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 97 b && fastAnswer E1 E2 W2 448 97 b == (97 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_97_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_97_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_97_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_97_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_97_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 97 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 97 b table_ok key.1, key.2]

theorem fast_98_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 98 (0 + b) && fastAnswer E1 E2 W2 448 98 (0 + b) == (98 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_98_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 98 (23 + b) && fastAnswer E1 E2 W2 448 98 (23 + b) == (98 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_98_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 98 (45 + b) && fastAnswer E1 E2 W2 448 98 (45 + b) == (98 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_98_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 98 (68 + b) && fastAnswer E1 E2 W2 448 98 (68 + b) == (98 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_98_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 98 (90 + b) && fastAnswer E1 E2 W2 448 98 (90 + b) == (98 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 98 of the addition table: the network answers (98 + b) % 113 for every b. -/
theorem row_98 : ∀ b, b < 113 → answer 98 b = (98 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 98 b && fastAnswer E1 E2 W2 448 98 b == (98 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_98_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_98_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_98_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_98_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_98_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 98 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 98 b table_ok key.1, key.2]

end PhaseGridInstances.P113Full

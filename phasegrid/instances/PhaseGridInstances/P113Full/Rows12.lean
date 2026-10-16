import PhaseGridInstances.P113Full.Table

/-! Rows 85 to 91 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Full

open LeanCheckedNetwork

theorem fast_85_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 85 (0 + b) && fastAnswer E1 E2 W2 448 85 (0 + b) == (85 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_85_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 85 (23 + b) && fastAnswer E1 E2 W2 448 85 (23 + b) == (85 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_85_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 85 (45 + b) && fastAnswer E1 E2 W2 448 85 (45 + b) == (85 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_85_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 85 (68 + b) && fastAnswer E1 E2 W2 448 85 (68 + b) == (85 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_85_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 85 (90 + b) && fastAnswer E1 E2 W2 448 85 (90 + b) == (85 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 85 of the addition table: the network answers (85 + b) % 113 for every b. -/
theorem row_85 : ∀ b, b < 113 → answer 85 b = (85 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 85 b && fastAnswer E1 E2 W2 448 85 b == (85 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_85_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_85_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_85_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_85_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_85_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 85 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 85 b table_ok key.1, key.2]

theorem fast_86_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 86 (0 + b) && fastAnswer E1 E2 W2 448 86 (0 + b) == (86 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_86_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 86 (23 + b) && fastAnswer E1 E2 W2 448 86 (23 + b) == (86 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_86_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 86 (45 + b) && fastAnswer E1 E2 W2 448 86 (45 + b) == (86 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_86_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 86 (68 + b) && fastAnswer E1 E2 W2 448 86 (68 + b) == (86 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_86_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 86 (90 + b) && fastAnswer E1 E2 W2 448 86 (90 + b) == (86 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 86 of the addition table: the network answers (86 + b) % 113 for every b. -/
theorem row_86 : ∀ b, b < 113 → answer 86 b = (86 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 86 b && fastAnswer E1 E2 W2 448 86 b == (86 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_86_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_86_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_86_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_86_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_86_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 86 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 86 b table_ok key.1, key.2]

theorem fast_87_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 87 (0 + b) && fastAnswer E1 E2 W2 448 87 (0 + b) == (87 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_87_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 87 (23 + b) && fastAnswer E1 E2 W2 448 87 (23 + b) == (87 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_87_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 87 (45 + b) && fastAnswer E1 E2 W2 448 87 (45 + b) == (87 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_87_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 87 (68 + b) && fastAnswer E1 E2 W2 448 87 (68 + b) == (87 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_87_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 87 (90 + b) && fastAnswer E1 E2 W2 448 87 (90 + b) == (87 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 87 of the addition table: the network answers (87 + b) % 113 for every b. -/
theorem row_87 : ∀ b, b < 113 → answer 87 b = (87 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 87 b && fastAnswer E1 E2 W2 448 87 b == (87 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_87_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_87_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_87_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_87_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_87_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 87 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 87 b table_ok key.1, key.2]

theorem fast_88_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 88 (0 + b) && fastAnswer E1 E2 W2 448 88 (0 + b) == (88 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_88_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 88 (23 + b) && fastAnswer E1 E2 W2 448 88 (23 + b) == (88 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_88_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 88 (45 + b) && fastAnswer E1 E2 W2 448 88 (45 + b) == (88 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_88_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 88 (68 + b) && fastAnswer E1 E2 W2 448 88 (68 + b) == (88 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_88_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 88 (90 + b) && fastAnswer E1 E2 W2 448 88 (90 + b) == (88 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 88 of the addition table: the network answers (88 + b) % 113 for every b. -/
theorem row_88 : ∀ b, b < 113 → answer 88 b = (88 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 88 b && fastAnswer E1 E2 W2 448 88 b == (88 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_88_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_88_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_88_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_88_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_88_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 88 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 88 b table_ok key.1, key.2]

theorem fast_89_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 89 (0 + b) && fastAnswer E1 E2 W2 448 89 (0 + b) == (89 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_89_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 89 (23 + b) && fastAnswer E1 E2 W2 448 89 (23 + b) == (89 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_89_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 89 (45 + b) && fastAnswer E1 E2 W2 448 89 (45 + b) == (89 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_89_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 89 (68 + b) && fastAnswer E1 E2 W2 448 89 (68 + b) == (89 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_89_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 89 (90 + b) && fastAnswer E1 E2 W2 448 89 (90 + b) == (89 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 89 of the addition table: the network answers (89 + b) % 113 for every b. -/
theorem row_89 : ∀ b, b < 113 → answer 89 b = (89 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 89 b && fastAnswer E1 E2 W2 448 89 b == (89 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_89_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_89_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_89_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_89_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_89_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 89 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 89 b table_ok key.1, key.2]

theorem fast_90_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 90 (0 + b) && fastAnswer E1 E2 W2 448 90 (0 + b) == (90 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_90_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 90 (23 + b) && fastAnswer E1 E2 W2 448 90 (23 + b) == (90 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_90_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 90 (45 + b) && fastAnswer E1 E2 W2 448 90 (45 + b) == (90 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_90_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 90 (68 + b) && fastAnswer E1 E2 W2 448 90 (68 + b) == (90 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_90_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 90 (90 + b) && fastAnswer E1 E2 W2 448 90 (90 + b) == (90 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 90 of the addition table: the network answers (90 + b) % 113 for every b. -/
theorem row_90 : ∀ b, b < 113 → answer 90 b = (90 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 90 b && fastAnswer E1 E2 W2 448 90 b == (90 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_90_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_90_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_90_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_90_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_90_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 90 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 90 b table_ok key.1, key.2]

theorem fast_91_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 91 (0 + b) && fastAnswer E1 E2 W2 448 91 (0 + b) == (91 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_91_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 91 (23 + b) && fastAnswer E1 E2 W2 448 91 (23 + b) == (91 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_91_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 91 (45 + b) && fastAnswer E1 E2 W2 448 91 (45 + b) == (91 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_91_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 91 (68 + b) && fastAnswer E1 E2 W2 448 91 (68 + b) == (91 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_91_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 91 (90 + b) && fastAnswer E1 E2 W2 448 91 (90 + b) == (91 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 91 of the addition table: the network answers (91 + b) % 113 for every b. -/
theorem row_91 : ∀ b, b < 113 → answer 91 b = (91 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 91 b && fastAnswer E1 E2 W2 448 91 b == (91 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_91_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_91_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_91_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_91_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_91_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 91 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 91 b table_ok key.1, key.2]

end PhaseGridInstances.P113Full

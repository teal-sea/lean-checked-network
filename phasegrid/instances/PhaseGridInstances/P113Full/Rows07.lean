import PhaseGridInstances.P113Full.Table

/-! Rows 50 to 56 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Full

open LeanCheckedNetwork

theorem fast_50_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 50 (0 + b) && fastAnswer E1 E2 W2 448 50 (0 + b) == (50 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_50_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 50 (23 + b) && fastAnswer E1 E2 W2 448 50 (23 + b) == (50 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_50_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 50 (45 + b) && fastAnswer E1 E2 W2 448 50 (45 + b) == (50 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_50_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 50 (68 + b) && fastAnswer E1 E2 W2 448 50 (68 + b) == (50 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_50_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 50 (90 + b) && fastAnswer E1 E2 W2 448 50 (90 + b) == (50 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 50 of the addition table: the network answers (50 + b) % 113 for every b. -/
theorem row_50 : ∀ b, b < 113 → answer 50 b = (50 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 50 b && fastAnswer E1 E2 W2 448 50 b == (50 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_50_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_50_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_50_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_50_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_50_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 50 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 50 b table_ok key.1, key.2]

theorem fast_51_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 51 (0 + b) && fastAnswer E1 E2 W2 448 51 (0 + b) == (51 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_51_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 51 (23 + b) && fastAnswer E1 E2 W2 448 51 (23 + b) == (51 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_51_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 51 (45 + b) && fastAnswer E1 E2 W2 448 51 (45 + b) == (51 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_51_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 51 (68 + b) && fastAnswer E1 E2 W2 448 51 (68 + b) == (51 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_51_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 51 (90 + b) && fastAnswer E1 E2 W2 448 51 (90 + b) == (51 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 51 of the addition table: the network answers (51 + b) % 113 for every b. -/
theorem row_51 : ∀ b, b < 113 → answer 51 b = (51 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 51 b && fastAnswer E1 E2 W2 448 51 b == (51 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_51_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_51_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_51_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_51_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_51_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 51 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 51 b table_ok key.1, key.2]

theorem fast_52_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 52 (0 + b) && fastAnswer E1 E2 W2 448 52 (0 + b) == (52 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_52_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 52 (23 + b) && fastAnswer E1 E2 W2 448 52 (23 + b) == (52 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_52_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 52 (45 + b) && fastAnswer E1 E2 W2 448 52 (45 + b) == (52 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_52_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 52 (68 + b) && fastAnswer E1 E2 W2 448 52 (68 + b) == (52 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_52_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 52 (90 + b) && fastAnswer E1 E2 W2 448 52 (90 + b) == (52 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 52 of the addition table: the network answers (52 + b) % 113 for every b. -/
theorem row_52 : ∀ b, b < 113 → answer 52 b = (52 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 52 b && fastAnswer E1 E2 W2 448 52 b == (52 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_52_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_52_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_52_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_52_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_52_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 52 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 52 b table_ok key.1, key.2]

theorem fast_53_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 53 (0 + b) && fastAnswer E1 E2 W2 448 53 (0 + b) == (53 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_53_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 53 (23 + b) && fastAnswer E1 E2 W2 448 53 (23 + b) == (53 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_53_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 53 (45 + b) && fastAnswer E1 E2 W2 448 53 (45 + b) == (53 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_53_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 53 (68 + b) && fastAnswer E1 E2 W2 448 53 (68 + b) == (53 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_53_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 53 (90 + b) && fastAnswer E1 E2 W2 448 53 (90 + b) == (53 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 53 of the addition table: the network answers (53 + b) % 113 for every b. -/
theorem row_53 : ∀ b, b < 113 → answer 53 b = (53 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 53 b && fastAnswer E1 E2 W2 448 53 b == (53 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_53_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_53_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_53_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_53_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_53_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 53 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 53 b table_ok key.1, key.2]

theorem fast_54_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 54 (0 + b) && fastAnswer E1 E2 W2 448 54 (0 + b) == (54 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_54_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 54 (23 + b) && fastAnswer E1 E2 W2 448 54 (23 + b) == (54 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_54_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 54 (45 + b) && fastAnswer E1 E2 W2 448 54 (45 + b) == (54 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_54_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 54 (68 + b) && fastAnswer E1 E2 W2 448 54 (68 + b) == (54 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_54_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 54 (90 + b) && fastAnswer E1 E2 W2 448 54 (90 + b) == (54 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 54 of the addition table: the network answers (54 + b) % 113 for every b. -/
theorem row_54 : ∀ b, b < 113 → answer 54 b = (54 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 54 b && fastAnswer E1 E2 W2 448 54 b == (54 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_54_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_54_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_54_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_54_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_54_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 54 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 54 b table_ok key.1, key.2]

theorem fast_55_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 55 (0 + b) && fastAnswer E1 E2 W2 448 55 (0 + b) == (55 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_55_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 55 (23 + b) && fastAnswer E1 E2 W2 448 55 (23 + b) == (55 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_55_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 55 (45 + b) && fastAnswer E1 E2 W2 448 55 (45 + b) == (55 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_55_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 55 (68 + b) && fastAnswer E1 E2 W2 448 55 (68 + b) == (55 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_55_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 55 (90 + b) && fastAnswer E1 E2 W2 448 55 (90 + b) == (55 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 55 of the addition table: the network answers (55 + b) % 113 for every b. -/
theorem row_55 : ∀ b, b < 113 → answer 55 b = (55 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 55 b && fastAnswer E1 E2 W2 448 55 b == (55 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_55_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_55_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_55_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_55_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_55_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 55 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 55 b table_ok key.1, key.2]

theorem fast_56_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 56 (0 + b) && fastAnswer E1 E2 W2 448 56 (0 + b) == (56 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_56_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 56 (23 + b) && fastAnswer E1 E2 W2 448 56 (23 + b) == (56 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_56_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 56 (45 + b) && fastAnswer E1 E2 W2 448 56 (45 + b) == (56 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_56_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 56 (68 + b) && fastAnswer E1 E2 W2 448 56 (68 + b) == (56 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_56_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 56 (90 + b) && fastAnswer E1 E2 W2 448 56 (90 + b) == (56 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 56 of the addition table: the network answers (56 + b) % 113 for every b. -/
theorem row_56 : ∀ b, b < 113 → answer 56 b = (56 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 56 b && fastAnswer E1 E2 W2 448 56 b == (56 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_56_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_56_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_56_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_56_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_56_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 56 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 56 b table_ok key.1, key.2]

end PhaseGridInstances.P113Full

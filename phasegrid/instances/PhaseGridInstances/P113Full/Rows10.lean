import PhaseGridInstances.P113Full.Table

/-! Rows 71 to 77 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Full

open LeanCheckedNetwork

theorem fast_71_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 71 (0 + b) && fastAnswer E1 E2 W2 448 71 (0 + b) == (71 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_71_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 71 (23 + b) && fastAnswer E1 E2 W2 448 71 (23 + b) == (71 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_71_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 71 (45 + b) && fastAnswer E1 E2 W2 448 71 (45 + b) == (71 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_71_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 71 (68 + b) && fastAnswer E1 E2 W2 448 71 (68 + b) == (71 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_71_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 71 (90 + b) && fastAnswer E1 E2 W2 448 71 (90 + b) == (71 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 71 of the addition table: the network answers (71 + b) % 113 for every b. -/
theorem row_71 : ∀ b, b < 113 → answer 71 b = (71 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 71 b && fastAnswer E1 E2 W2 448 71 b == (71 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_71_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_71_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_71_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_71_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_71_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 71 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 71 b table_ok key.1, key.2]

theorem fast_72_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 72 (0 + b) && fastAnswer E1 E2 W2 448 72 (0 + b) == (72 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_72_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 72 (23 + b) && fastAnswer E1 E2 W2 448 72 (23 + b) == (72 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_72_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 72 (45 + b) && fastAnswer E1 E2 W2 448 72 (45 + b) == (72 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_72_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 72 (68 + b) && fastAnswer E1 E2 W2 448 72 (68 + b) == (72 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_72_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 72 (90 + b) && fastAnswer E1 E2 W2 448 72 (90 + b) == (72 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 72 of the addition table: the network answers (72 + b) % 113 for every b. -/
theorem row_72 : ∀ b, b < 113 → answer 72 b = (72 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 72 b && fastAnswer E1 E2 W2 448 72 b == (72 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_72_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_72_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_72_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_72_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_72_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 72 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 72 b table_ok key.1, key.2]

theorem fast_73_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 73 (0 + b) && fastAnswer E1 E2 W2 448 73 (0 + b) == (73 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_73_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 73 (23 + b) && fastAnswer E1 E2 W2 448 73 (23 + b) == (73 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_73_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 73 (45 + b) && fastAnswer E1 E2 W2 448 73 (45 + b) == (73 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_73_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 73 (68 + b) && fastAnswer E1 E2 W2 448 73 (68 + b) == (73 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_73_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 73 (90 + b) && fastAnswer E1 E2 W2 448 73 (90 + b) == (73 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 73 of the addition table: the network answers (73 + b) % 113 for every b. -/
theorem row_73 : ∀ b, b < 113 → answer 73 b = (73 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 73 b && fastAnswer E1 E2 W2 448 73 b == (73 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_73_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_73_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_73_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_73_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_73_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 73 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 73 b table_ok key.1, key.2]

theorem fast_74_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 74 (0 + b) && fastAnswer E1 E2 W2 448 74 (0 + b) == (74 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_74_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 74 (23 + b) && fastAnswer E1 E2 W2 448 74 (23 + b) == (74 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_74_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 74 (45 + b) && fastAnswer E1 E2 W2 448 74 (45 + b) == (74 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_74_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 74 (68 + b) && fastAnswer E1 E2 W2 448 74 (68 + b) == (74 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_74_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 74 (90 + b) && fastAnswer E1 E2 W2 448 74 (90 + b) == (74 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 74 of the addition table: the network answers (74 + b) % 113 for every b. -/
theorem row_74 : ∀ b, b < 113 → answer 74 b = (74 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 74 b && fastAnswer E1 E2 W2 448 74 b == (74 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_74_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_74_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_74_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_74_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_74_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 74 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 74 b table_ok key.1, key.2]

theorem fast_75_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 75 (0 + b) && fastAnswer E1 E2 W2 448 75 (0 + b) == (75 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_75_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 75 (23 + b) && fastAnswer E1 E2 W2 448 75 (23 + b) == (75 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_75_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 75 (45 + b) && fastAnswer E1 E2 W2 448 75 (45 + b) == (75 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_75_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 75 (68 + b) && fastAnswer E1 E2 W2 448 75 (68 + b) == (75 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_75_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 75 (90 + b) && fastAnswer E1 E2 W2 448 75 (90 + b) == (75 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 75 of the addition table: the network answers (75 + b) % 113 for every b. -/
theorem row_75 : ∀ b, b < 113 → answer 75 b = (75 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 75 b && fastAnswer E1 E2 W2 448 75 b == (75 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_75_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_75_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_75_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_75_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_75_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 75 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 75 b table_ok key.1, key.2]

theorem fast_76_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 76 (0 + b) && fastAnswer E1 E2 W2 448 76 (0 + b) == (76 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_76_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 76 (23 + b) && fastAnswer E1 E2 W2 448 76 (23 + b) == (76 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_76_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 76 (45 + b) && fastAnswer E1 E2 W2 448 76 (45 + b) == (76 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_76_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 76 (68 + b) && fastAnswer E1 E2 W2 448 76 (68 + b) == (76 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_76_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 76 (90 + b) && fastAnswer E1 E2 W2 448 76 (90 + b) == (76 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 76 of the addition table: the network answers (76 + b) % 113 for every b. -/
theorem row_76 : ∀ b, b < 113 → answer 76 b = (76 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 76 b && fastAnswer E1 E2 W2 448 76 b == (76 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_76_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_76_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_76_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_76_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_76_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 76 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 76 b table_ok key.1, key.2]

theorem fast_77_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 77 (0 + b) && fastAnswer E1 E2 W2 448 77 (0 + b) == (77 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_77_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 77 (23 + b) && fastAnswer E1 E2 W2 448 77 (23 + b) == (77 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_77_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 77 (45 + b) && fastAnswer E1 E2 W2 448 77 (45 + b) == (77 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_77_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 77 (68 + b) && fastAnswer E1 E2 W2 448 77 (68 + b) == (77 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_77_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 77 (90 + b) && fastAnswer E1 E2 W2 448 77 (90 + b) == (77 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 77 of the addition table: the network answers (77 + b) % 113 for every b. -/
theorem row_77 : ∀ b, b < 113 → answer 77 b = (77 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 77 b && fastAnswer E1 E2 W2 448 77 b == (77 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_77_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_77_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_77_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_77_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_77_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 77 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 77 b table_ok key.1, key.2]

end PhaseGridInstances.P113Full

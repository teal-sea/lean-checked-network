import PhaseGridInstances.P113Full.Table

/-! Rows 106 to 112 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

set_option Elab.async false

namespace PhaseGridInstances.P113Full

open LeanCheckedNetwork

theorem fast_106_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 106 (0 + b) && fastAnswer E1 E2 W2 448 106 (0 + b) == (106 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_106_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 106 (23 + b) && fastAnswer E1 E2 W2 448 106 (23 + b) == (106 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_106_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 106 (45 + b) && fastAnswer E1 E2 W2 448 106 (45 + b) == (106 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_106_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 106 (68 + b) && fastAnswer E1 E2 W2 448 106 (68 + b) == (106 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_106_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 106 (90 + b) && fastAnswer E1 E2 W2 448 106 (90 + b) == (106 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 106 of the addition table: the network answers (106 + b) % 113 for every b. -/
theorem row_106 : ∀ b, b < 113 → answer 106 b = (106 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 106 b && fastAnswer E1 E2 W2 448 106 b == (106 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_106_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_106_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_106_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_106_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_106_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 106 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 106 b table_ok key.1, key.2]

theorem fast_107_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 107 (0 + b) && fastAnswer E1 E2 W2 448 107 (0 + b) == (107 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_107_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 107 (23 + b) && fastAnswer E1 E2 W2 448 107 (23 + b) == (107 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_107_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 107 (45 + b) && fastAnswer E1 E2 W2 448 107 (45 + b) == (107 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_107_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 107 (68 + b) && fastAnswer E1 E2 W2 448 107 (68 + b) == (107 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_107_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 107 (90 + b) && fastAnswer E1 E2 W2 448 107 (90 + b) == (107 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 107 of the addition table: the network answers (107 + b) % 113 for every b. -/
theorem row_107 : ∀ b, b < 113 → answer 107 b = (107 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 107 b && fastAnswer E1 E2 W2 448 107 b == (107 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_107_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_107_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_107_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_107_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_107_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 107 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 107 b table_ok key.1, key.2]

theorem fast_108_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 108 (0 + b) && fastAnswer E1 E2 W2 448 108 (0 + b) == (108 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_108_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 108 (23 + b) && fastAnswer E1 E2 W2 448 108 (23 + b) == (108 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_108_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 108 (45 + b) && fastAnswer E1 E2 W2 448 108 (45 + b) == (108 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_108_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 108 (68 + b) && fastAnswer E1 E2 W2 448 108 (68 + b) == (108 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_108_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 108 (90 + b) && fastAnswer E1 E2 W2 448 108 (90 + b) == (108 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 108 of the addition table: the network answers (108 + b) % 113 for every b. -/
theorem row_108 : ∀ b, b < 113 → answer 108 b = (108 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 108 b && fastAnswer E1 E2 W2 448 108 b == (108 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_108_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_108_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_108_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_108_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_108_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 108 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 108 b table_ok key.1, key.2]

theorem fast_109_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 109 (0 + b) && fastAnswer E1 E2 W2 448 109 (0 + b) == (109 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_109_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 109 (23 + b) && fastAnswer E1 E2 W2 448 109 (23 + b) == (109 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_109_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 109 (45 + b) && fastAnswer E1 E2 W2 448 109 (45 + b) == (109 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_109_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 109 (68 + b) && fastAnswer E1 E2 W2 448 109 (68 + b) == (109 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_109_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 109 (90 + b) && fastAnswer E1 E2 W2 448 109 (90 + b) == (109 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 109 of the addition table: the network answers (109 + b) % 113 for every b. -/
theorem row_109 : ∀ b, b < 113 → answer 109 b = (109 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 109 b && fastAnswer E1 E2 W2 448 109 b == (109 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_109_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_109_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_109_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_109_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_109_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 109 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 109 b table_ok key.1, key.2]

theorem fast_110_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 110 (0 + b) && fastAnswer E1 E2 W2 448 110 (0 + b) == (110 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_110_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 110 (23 + b) && fastAnswer E1 E2 W2 448 110 (23 + b) == (110 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_110_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 110 (45 + b) && fastAnswer E1 E2 W2 448 110 (45 + b) == (110 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_110_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 110 (68 + b) && fastAnswer E1 E2 W2 448 110 (68 + b) == (110 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_110_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 110 (90 + b) && fastAnswer E1 E2 W2 448 110 (90 + b) == (110 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 110 of the addition table: the network answers (110 + b) % 113 for every b. -/
theorem row_110 : ∀ b, b < 113 → answer 110 b = (110 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 110 b && fastAnswer E1 E2 W2 448 110 b == (110 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_110_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_110_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_110_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_110_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_110_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 110 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 110 b table_ok key.1, key.2]

theorem fast_111_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 111 (0 + b) && fastAnswer E1 E2 W2 448 111 (0 + b) == (111 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_111_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 111 (23 + b) && fastAnswer E1 E2 W2 448 111 (23 + b) == (111 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_111_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 111 (45 + b) && fastAnswer E1 E2 W2 448 111 (45 + b) == (111 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_111_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 111 (68 + b) && fastAnswer E1 E2 W2 448 111 (68 + b) == (111 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_111_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 111 (90 + b) && fastAnswer E1 E2 W2 448 111 (90 + b) == (111 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 111 of the addition table: the network answers (111 + b) % 113 for every b. -/
theorem row_111 : ∀ b, b < 113 → answer 111 b = (111 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 111 b && fastAnswer E1 E2 W2 448 111 b == (111 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_111_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_111_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_111_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_111_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_111_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 111 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 111 b table_ok key.1, key.2]

theorem fast_112_0 : ∀ b, b < 23 →
    (fastOk E1 E2 448 112 (0 + b) && fastAnswer E1 E2 W2 448 112 (0 + b) == (112 + (0 + b)) % 113) = true := by
  decide +kernel

theorem fast_112_1 : ∀ b, b < 22 →
    (fastOk E1 E2 448 112 (23 + b) && fastAnswer E1 E2 W2 448 112 (23 + b) == (112 + (23 + b)) % 113) = true := by
  decide +kernel

theorem fast_112_2 : ∀ b, b < 23 →
    (fastOk E1 E2 448 112 (45 + b) && fastAnswer E1 E2 W2 448 112 (45 + b) == (112 + (45 + b)) % 113) = true := by
  decide +kernel

theorem fast_112_3 : ∀ b, b < 22 →
    (fastOk E1 E2 448 112 (68 + b) && fastAnswer E1 E2 W2 448 112 (68 + b) == (112 + (68 + b)) % 113) = true := by
  decide +kernel

theorem fast_112_4 : ∀ b, b < 23 →
    (fastOk E1 E2 448 112 (90 + b) && fastAnswer E1 E2 W2 448 112 (90 + b) == (112 + (90 + b)) % 113) = true := by
  decide +kernel

/-- Row 112 of the addition table: the network answers (112 + b) % 113 for every b. -/
theorem row_112 : ∀ b, b < 113 → answer 112 b = (112 + b) % 113 := by
  intro b hb
  have key : (fastOk E1 E2 448 112 b && fastAnswer E1 E2 W2 448 112 b == (112 + b) % 113) = true := by
    rcases Nat.lt_or_ge b 23 with h0 | h0
    · have h := fast_112_0 (b - 0) (by omega); rwa [show 0 + (b - 0) = b by omega] at h
    rcases Nat.lt_or_ge b 45 with h1 | h1
    · have h := fast_112_1 (b - 23) (by omega); rwa [show 23 + (b - 23) = b by omega] at h
    rcases Nat.lt_or_ge b 68 with h2 | h2
    · have h := fast_112_2 (b - 45) (by omega); rwa [show 45 + (b - 45) = b by omega] at h
    rcases Nat.lt_or_ge b 90 with h3 | h3
    · have h := fast_112_3 (b - 68) (by omega); rwa [show 68 + (b - 68) = b by omega] at h
    have h := fast_112_4 (b - 90) (by omega); rwa [show 90 + (b - 90) = b by omega] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at key
  show LeanCheckedNetwork.answer E1 E2 W2 112 b = _
  rw [answer_eq_fastAnswer E1 E2 W2 448 112 b table_ok key.1, key.2]

end PhaseGridInstances.P113Full

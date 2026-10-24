import Mathlib
namespace Profile

/-- Signed Euclidean quotient. The profile admits positive divisors only. -/
def floorDiv (a d : ℤ) : ℤ := a / d
def ceilDiv (a d : ℤ) : ℤ := -((-a) / d)

theorem floorDiv_bounds (a d : ℤ) (hd : 0 < d) :
    floorDiv a d * d ≤ a ∧ a < (floorDiv a d + 1) * d := by
  exact ⟨Int.ediv_mul_le a (ne_of_gt hd), Int.lt_ediv_add_one_mul_self a hd⟩

theorem ceilDiv_bounds (a d : ℤ) (hd : 0 < d) :
    (ceilDiv a d - 1) * d < a ∧ a ≤ ceilDiv a d * d := by
  have h := floorDiv_bounds (-a) d hd
  dsimp [floorDiv, ceilDiv] at *
  constructor <;> nlinarith [h.1, h.2]

/-- Real-valued specification of rounding to the scale 2^-s. -/
def scale (s : ℕ) : ℝ := (2 : ℝ)^s
noncomputable def down (s : ℕ) (x : ℝ) : ℝ := (⌊x * scale s⌋ : ℤ) / scale s
noncomputable def up (s : ℕ) (x : ℝ) : ℝ := (⌈x * scale s⌉ : ℤ) / scale s

theorem scale_pos (s : ℕ) : 0 < scale s := by
  unfold scale
  positivity

theorem down_le (s : ℕ) (x : ℝ) : down s x ≤ x := by
  apply (div_le_iff₀ (scale_pos s)).2
  exact Int.floor_le _

theorem le_up (s : ℕ) (x : ℝ) : x ≤ up s x := by
  apply (le_div_iff₀ (scale_pos s)).2
  exact Int.le_ceil _

theorem down_gap (s : ℕ) (x : ℝ) : x - down s x < 1 / scale s := by
  have h := Int.lt_floor_add_one (x * scale s)
  have hs := scale_pos s
  dsimp [down]
  apply (lt_div_iff₀ hs).2
  field_simp
  nlinarith

theorem up_gap (s : ℕ) (x : ℝ) : up s x - x < 1 / scale s := by
  have h := Int.ceil_lt_add_one (x * scale s)
  have hs := scale_pos s
  dsimp [up]
  apply (lt_div_iff₀ hs).2
  field_simp
  nlinarith

/-- Executable signed integer division bounds interpreted in the reals. -/
theorem floorDiv_real (a d : ℤ) (hd : 0 < d) :
    (floorDiv a d : ℝ) ≤ (a : ℝ)/(d : ℝ) ∧
    (a : ℝ)/(d : ℝ) < (floorDiv a d : ℝ)+1 := by
  have h := floorDiv_bounds a d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · apply (le_div_iff₀ hdR).2
    exact_mod_cast h.1
  · apply (div_lt_iff₀ hdR).2
    exact_mod_cast h.2

theorem ceilDiv_real (a d : ℤ) (hd : 0 < d) :
    (ceilDiv a d : ℝ)-1 < (a : ℝ)/(d : ℝ) ∧
    (a : ℝ)/(d : ℝ) ≤ (ceilDiv a d : ℝ) := by
  have h := ceilDiv_bounds a d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · apply (lt_div_iff₀ hdR).2
    exact_mod_cast h.1
  · apply (div_le_iff₀ hdR).2
    exact_mod_cast h.2

/-- The executable n/d -> integer-grid rule encloses the original rational. -/
theorem integer_rounding (n d : ℤ) (s : ℕ) (hd : 0 < d) :
    (floorDiv (n * 2^s) d : ℝ) / scale s ≤ (n : ℝ)/(d : ℝ) ∧
    (n : ℝ)/(d : ℝ) ≤ (ceilDiv (n * 2^s) d : ℝ) / scale s := by
  have hf := floorDiv_real (n * 2^s) d hd
  have hc := ceilDiv_real (n * 2^s) d hd
  have he : ((n * 2^s : ℤ) : ℝ) = (n : ℝ) * scale s := by simp [scale]
  rw [he] at hf hc
  constructor
  · apply (div_le_iff₀ (scale_pos s)).2
    simpa only [mul_div_right_comm] using hf.1
  · apply (le_div_iff₀ (scale_pos s)).2
    simpa only [mul_div_right_comm] using hc.2

/-- Both arguments may be signed and may cross zero. -/
def pLo (a b c d : ℝ) : ℝ := min (min (a*c) (a*d)) (min (b*c) (b*d))
def pHi (a b c d : ℝ) : ℝ := max (max (a*c) (a*d)) (max (b*c) (b*d))

theorem mul_between {a b x z : ℝ} (hx : a ≤ x ∧ x ≤ b) :
    min (a*z) (b*z) ≤ x*z ∧ x*z ≤ max (a*z) (b*z) := by
  rcases le_total 0 z with hz | hz
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hz),
      (mul_le_mul_of_nonneg_right hx.2 hz).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hz),
      (mul_le_mul_of_nonpos_right hx.1 hz).trans (le_max_left _ _)⟩

theorem product_bounds {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (hy : c ≤ y ∧ y ≤ d) : pLo a b c d ≤ x*y ∧ x*y ≤ pHi a b c d := by
  have ha := mul_between (z := a) hy
  have hb := mul_between (z := b) hy
  simp only [mul_comm _ a] at ha
  simp only [mul_comm _ b] at hb
  have h := mul_between (z := y) hx
  constructor
  · apply le_trans _ h.1
    apply le_min
    · exact (min_le_left _ _).trans ha.1
    · exact (min_le_right _ _).trans hb.1
  · apply le_trans h.2
    apply max_le
    · exact ha.2.trans (le_max_left _ _)
    · exact hb.2.trans (le_max_right _ _)

theorem rounded_sum {a b c d x y : ℝ} (s : ℕ)
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    down s (a+c) ≤ x+y ∧ x+y ≤ up s (b+d) :=
  ⟨(down_le _ _).trans (add_le_add hx.1 hy.1),
   (add_le_add hx.2 hy.2).trans (le_up _ _)⟩

theorem rounded_product {a b c d x y : ℝ} (s : ℕ)
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    down s (pLo a b c d) ≤ x*y ∧ x*y ≤ up s (pHi a b c d) := by
  have h := product_bounds hx hy
  exact ⟨(down_le _ _).trans h.1, h.2.trans (le_up _ _)⟩

theorem relu_lower {α x : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    α*x ≤ max 0 x := by
  rcases le_total x 0 with hx | hx
  · rw [max_eq_left hx]
    exact mul_nonpos_of_nonneg_of_nonpos h0 hx
  · rw [max_eq_right hx]
    nlinarith

/-- Crossing-zero secant; stable intervals use zero or identity exactly. -/
theorem relu_secant {l u x : ℝ} (hl : l < 0) (hu : 0 < u)
    (hx : l ≤ x ∧ x ≤ u) : max 0 x ≤ (u/(u-l))*(x-l) := by
  have hd : 0 < u-l := by linarith
  apply max_le
  · exact mul_nonneg (div_nonneg (le_of_lt hu) (le_of_lt hd)) (sub_nonneg.mpr hx.1)
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).2
    nlinarith [mul_nonneg (neg_nonneg.mpr (le_of_lt hl)) (sub_nonneg.mpr hx.2)]

theorem relu_interval {l u x : ℝ} (hx : l ≤ x ∧ x ≤ u) :
    max 0 l ≤ max 0 x ∧ max 0 x ≤ max 0 u :=
  ⟨max_le_max le_rfl hx.1, max_le_max le_rfl hx.2⟩

theorem relu_inactive {u x : ℝ} (hx : x ≤ u) (hu : u ≤ 0) : max 0 x = 0 :=
  max_eq_left (hx.trans hu)

theorem relu_active {l x : ℝ} (hx : l ≤ x) (hl : 0 ≤ l) : max 0 x = x :=
  max_eq_right (hl.trans hx)

theorem intersection {a b c d x : ℝ} (h : a ≤ x ∧ x ≤ b)
    (k : c ≤ x ∧ x ≤ d) : max a c ≤ x ∧ x ≤ min b d :=
  ⟨max_le h.1 k.1, le_min h.2 k.2⟩

#print axioms floorDiv_bounds
#print axioms ceilDiv_bounds
#print axioms scale_pos
#print axioms down_le
#print axioms le_up
#print axioms down_gap
#print axioms up_gap
#print axioms floorDiv_real
#print axioms ceilDiv_real
#print axioms relu_interval
#print axioms relu_inactive
#print axioms relu_active
#print axioms integer_rounding
#print axioms mul_between
#print axioms product_bounds
#print axioms rounded_sum
#print axioms rounded_product
#print axioms relu_lower
#print axioms relu_secant
#print axioms intersection
end Profile

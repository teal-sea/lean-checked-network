import Mathlib

/-!
# `expFix`: an integer stand-in for `2^f * exp (x / 2^t)`, with a proved error bound

This is Theorem B1 of `transformer/DESIGN.md`. For an integer `x ≤ 0` and parameters
`t f n m R`, the integer program computes

    expFix x = 0                                        if x < -R 2^t
    expFix x = ⌊ 2^f N^(2^m) / F^(2^m) ⌋                otherwise,

with `N = Σ_{i<n} c_i x^i`, `c_i = (n-1)!/i! 2^((t+m)(n-1-i))` (Horner) and
`F = (n-1)! 2^((t+m)(n-1))`, so that `N/F = Σ_{i<n} y^i/i!` with `y = x/2^(t+m)` exactly.
The power is taken on the natural number `N.natAbs` (`2^m` is even, so this is `N^(2^m)`),
and the one division is a natural-number division. `expFix_close` bounds
`|expFix x - 2^f exp(x/2^t)|` by `deltaBound`, and `expFix_close_chosen` instantiates the
chosen parameters `(t, f, n, m, R) = (32, 32, 16, 5, 24)` with the bound `2`.
-/

namespace Transformer

/-- The parameters of `expFix`: `t` the input unit (`x` means `x / 2^t`), `f` the output scale
(`2^f`), `n` the number of Taylor terms, `m` the number of squarings (range reduction), `R` the
clamp (`expFix x = 0` for `x < -R 2^t`). -/
structure ExpParams where
  t : ℕ
  f : ℕ
  n : ℕ
  m : ℕ
  R : ℕ

/-- Horner evaluation: `horner [c₀, c₁, …] x = c₀ + x * (c₁ + x * (…))`, so it equals
`Σ cᵢ xⁱ`. This is the loop `N = N * x + c[i]` for `i = n-1, …, 0` of `int_transformer.py`. -/
def horner : List ℕ → ℤ → ℤ
  | [], _ => 0
  | c :: cs, x => (c : ℤ) + x * horner cs x

/-- `cᵢ = (n-1)!/i! · 2^((t+m)(n-1-i))`; the division is exact for `i < n`. -/
def coeff (p : ExpParams) (i : ℕ) : ℕ :=
  (p.n - 1).factorial / i.factorial * 2 ^ ((p.t + p.m) * (p.n - 1 - i))

/-- `[c₀, …, c_{n-1}]`. -/
def coeffs (p : ExpParams) : List ℕ := (List.range p.n).map (coeff p)

/-- `F = (n-1)! · 2^((t+m)(n-1))`. -/
def bigF (p : ExpParams) : ℕ := (p.n - 1).factorial * 2 ^ ((p.t + p.m) * (p.n - 1))

/-- The integer exponential: `expFix p x` approximates `2^f * exp (x / 2^t)` for `x ≤ 0`. -/
def expFix (p : ExpParams) (x : ℤ) : ℕ :=
  if x < -((p.R : ℤ) * 2 ^ p.t) then 0
  else 2 ^ p.f * (horner (coeffs p) x).natAbs ^ 2 ^ p.m / bigF p ^ 2 ^ p.m

/-- The Taylor remainder constant of `Real.exp_bound`: `τ(n) = (n+1) / (n! n)`. -/
noncomputable def tau (n : ℕ) : ℝ := (n + 1) / (n.factorial * n)

/-- The error bound of `expFix`: `2^f 2^m τ (1+τ)^(2^m - 1) + 1`. -/
noncomputable def deltaBound (p : ExpParams) : ℝ :=
  2 ^ p.f * 2 ^ p.m * tau p.n * (1 + tau p.n) ^ (2 ^ p.m - 1) + 1

/-- The chosen parameters: `t = 32` (so `q = 8`), `f = 32`, `n = 16`, `m = 5`, `R = 24`. -/
def chosen : ExpParams := ⟨32, 32, 16, 5, 24⟩

theorem horner_map_range (x : ℤ) :
    ∀ (k : ℕ) (g : ℕ → ℕ),
      horner ((List.range k).map g) x = ∑ i ∈ Finset.range k, (g i : ℤ) * x ^ i := by
  intro k
  induction k with
  | zero => intro g; simp [horner]
  | succ k ih =>
    intro g
    rw [List.range_succ_eq_map, List.map_cons, horner, List.map_map, ih (g ∘ Nat.succ),
      Finset.sum_range_succ']
    simp only [Function.comp_def, pow_zero, mul_one, Finset.mul_sum]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem coeff_div_bigF (p : ExpParams) (i : ℕ) (hi : i < p.n) :
    ((coeff p i : ℕ) : ℝ) / (bigF p : ℕ) = 1 / (i.factorial * 2 ^ ((p.t + p.m) * i)) := by
  have hdvd : i.factorial ∣ (p.n - 1).factorial := Nat.factorial_dvd_factorial (by omega)
  have hsplit : (p.t + p.m) * (p.n - 1) = (p.t + p.m) * (p.n - 1 - i) + (p.t + p.m) * i := by
    rw [← Nat.mul_add]; congr 1; omega
  unfold coeff bigF
  rw [hsplit, pow_add, Nat.cast_mul, Nat.cast_div hdvd (by positivity), Nat.cast_mul,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  have h1 : (i.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((p.n - 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

theorem horner_div_bigF (p : ExpParams) (x : ℤ) :
    ((horner (coeffs p) x : ℤ) : ℝ) / (bigF p : ℕ) =
      ∑ i ∈ Finset.range p.n, ((x : ℝ) / 2 ^ (p.t + p.m)) ^ i / i.factorial := by
  unfold coeffs
  rw [horner_map_range]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have h := coeff_div_bigF p i hi
  have h1 : (i.factorial : ℝ) ≠ 0 := by positivity
  rw [div_pow, ← pow_mul]
  calc ((coeff p i : ℕ) : ℝ) * (x : ℝ) ^ i / (bigF p : ℕ)
      = ((coeff p i : ℕ) : ℝ) / (bigF p : ℕ) * (x : ℝ) ^ i := by ring
    _ = 1 / (i.factorial * 2 ^ ((p.t + p.m) * i)) * (x : ℝ) ^ i := by rw [h]
    _ = (x : ℝ) ^ i / 2 ^ ((p.t + p.m) * i) / i.factorial := by field_simp

/-- `|a^(j+1) - b^(j+1)| ≤ (j+1) ε M^j` when `|a|, |b| ≤ M` and `|a - b| ≤ ε`. -/
theorem abs_pow_sub_pow_le {a b M ε : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M) (hab : |a - b| ≤ ε) :
    ∀ j : ℕ, |a ^ (j + 1) - b ^ (j + 1)| ≤ (j + 1) * ε * M ^ j := by
  have hM : 0 ≤ M := (abs_nonneg a).trans ha
  have hε : 0 ≤ ε := (abs_nonneg _).trans hab
  intro j
  induction j with
  | zero => simpa using hab
  | succ j ih =>
    have key : a ^ (j + 1 + 1) - b ^ (j + 1 + 1)
        = a * (a ^ (j + 1) - b ^ (j + 1)) + (a - b) * b ^ (j + 1) := by ring
    have hbp : |b ^ (j + 1)| ≤ M ^ (j + 1) := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg b) hb _
    rw [key]
    calc |a * (a ^ (j + 1) - b ^ (j + 1)) + (a - b) * b ^ (j + 1)|
        ≤ |a * (a ^ (j + 1) - b ^ (j + 1))| + |(a - b) * b ^ (j + 1)| := abs_add_le _ _
      _ = |a| * |a ^ (j + 1) - b ^ (j + 1)| + |a - b| * |b ^ (j + 1)| := by rw [abs_mul, abs_mul]
      _ ≤ M * ((j + 1) * ε * M ^ j) + ε * M ^ (j + 1) := by gcongr
      _ = ((j + 1 : ℕ) + 1) * ε * M ^ (j + 1) := by push_cast; ring

/-- A natural-number quotient is within less than `1` below the real quotient. -/
theorem natDiv_close (A B : ℕ) (hB : 0 < B) :
    |((A / B : ℕ) : ℝ) - (A : ℝ) / B| < 1 := by
  have h := Nat.div_add_mod A B
  have hmod := Nat.mod_lt A hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hA : (A : ℝ) = B * ((A / B : ℕ) : ℝ) + ((A % B : ℕ) : ℝ) := by exact_mod_cast h.symm
  have hr0 : (0 : ℝ) ≤ ((A % B : ℕ) : ℝ) / B := by positivity
  have hr1 : ((A % B : ℕ) : ℝ) / B < 1 := by
    rw [div_lt_one₀ hBr]; exact_mod_cast hmod
  rw [hA, add_div, mul_div_cancel_left₀ _ hBr.ne', abs_sub_lt_iff]
  constructor <;> linarith

/-- **Theorem B1.** For every integer `x ≤ 0`, `expFix p x` is within `deltaBound p` of
`2^f exp (x / 2^t)`, provided `0 < n`, `0 < m`, `R ≤ 2^m` and `2^f ≤ exp R`. -/
theorem expFix_close (p : ExpParams) (hn : 0 < p.n) (hm : 0 < p.m) (hR : p.R ≤ 2 ^ p.m)
    (hclamp : (2 : ℝ) ^ p.f ≤ Real.exp p.R) (x : ℤ) (hx : x ≤ 0) :
    |(expFix p x : ℝ) - 2 ^ p.f * Real.exp (x / 2 ^ p.t)| ≤ deltaBound p := by
  have htau : 0 ≤ tau p.n := by unfold tau; positivity
  have hdelta1 : 1 ≤ deltaBound p := by
    unfold deltaBound
    have : 0 ≤ (2 : ℝ) ^ p.f * 2 ^ p.m * tau p.n * (1 + tau p.n) ^ (2 ^ p.m - 1) := by positivity
    linarith
  unfold expFix
  split_ifs with hlt
  · -- below the clamp: the output is 0 and the true value is below 2^f exp(-R) ≤ 1
    simp only [Nat.cast_zero, zero_sub, abs_neg]
    rw [abs_of_pos (by positivity)]
    have hx' : (x : ℝ) / 2 ^ p.t < -(p.R : ℝ) := by
      have h1 : (x : ℝ) < -((p.R : ℝ) * 2 ^ p.t) := by exact_mod_cast hlt
      rw [div_lt_iff₀ (by positivity)]; linarith
    have h2 : Real.exp (x / 2 ^ p.t) < Real.exp (-(p.R : ℝ)) := Real.exp_lt_exp.2 hx'
    have h3 : (2 : ℝ) ^ p.f * Real.exp (-(p.R : ℝ)) ≤ 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one₀ (Real.exp_pos _)]; exact hclamp
    calc (2 : ℝ) ^ p.f * Real.exp (x / 2 ^ p.t) ≤ 2 ^ p.f * Real.exp (-(p.R : ℝ)) := by gcongr
      _ ≤ 1 := h3
      _ ≤ deltaBound p := hdelta1
  · -- in range
    rw [not_lt] at hlt
    set K := 2 ^ p.m with hK
    set N := horner (coeffs p) x with hN
    set y : ℝ := (x : ℝ) / 2 ^ (p.t + p.m) with hy
    set T : ℝ := ∑ i ∈ Finset.range p.n, y ^ i / i.factorial with hT
    have hy0 : y ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hx) (by positivity)
    have hy1 : -1 ≤ y := by
      rw [hy, le_div_iff₀ (by positivity)]
      have h1 : -((p.R : ℝ) * 2 ^ p.t) ≤ x := by exact_mod_cast hlt
      have h2 : (p.R : ℝ) ≤ 2 ^ p.m := by exact_mod_cast hR
      rw [pow_add]
      nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) p.t]
    have hyabs : |y| ≤ 1 := abs_le.2 ⟨hy1, by linarith⟩
    have hTaylor : |Real.exp y - T| ≤ tau p.n := by
      have h := Real.exp_bound hyabs hn
      refine h.trans ?_
      unfold tau
      have h1 : |y| ^ p.n ≤ 1 := pow_le_one₀ (abs_nonneg _) hyabs
      have hpos : 0 ≤ ((p.n.succ : ℝ) / (p.n.factorial * p.n)) := by positivity
      calc |y| ^ p.n * ((p.n.succ : ℝ) / (p.n.factorial * p.n))
          ≤ 1 * ((p.n.succ : ℝ) / (p.n.factorial * p.n)) := by gcongr
        _ = _ := by push_cast; ring
    have hexpy1 : Real.exp y ≤ 1 := Real.exp_le_one_iff.2 hy0
    have hexpy0 : 0 < Real.exp y := Real.exp_pos y
    have hTabs : |T| ≤ 1 + tau p.n := by
      calc |T| = |Real.exp y - (Real.exp y - T)| := by ring_nf
        _ ≤ |Real.exp y| + |Real.exp y - T| := abs_sub _ _
        _ ≤ 1 + tau p.n := by rw [abs_of_pos hexpy0]; gcongr
    have hEabs : |Real.exp y| ≤ 1 + tau p.n := by rw [abs_of_pos hexpy0]; linarith
    have hTE : |T - Real.exp y| ≤ tau p.n := by rw [abs_sub_comm]; exact hTaylor
    have hKpos : 0 < K := by positivity
    have hpow : |T ^ K - Real.exp y ^ K| ≤ K * tau p.n * (1 + tau p.n) ^ (K - 1) := by
      obtain ⟨j, hj⟩ : ∃ j, K = j + 1 := ⟨K - 1, by omega⟩
      rw [hj, Nat.add_sub_cancel]
      have := abs_pow_sub_pow_le hTabs hEabs hTE j
      push_cast
      exact this
    have hexpK : Real.exp y ^ K = Real.exp (x / 2 ^ p.t) := by
      rw [← Real.exp_nat_mul, hy, hK]
      congr 1
      rw [pow_add]
      field_simp
      push_cast
      ring
    have hNF : ((N : ℤ) : ℝ) / (bigF p : ℕ) = T := horner_div_bigF p x
    have hFpos : 0 < bigF p := by unfold bigF; positivity
    have hKeven : Even K := by
      rw [hK]; exact (Nat.even_pow).2 ⟨even_two, hm.ne'⟩
    have hcastAbs : ((N.natAbs : ℕ) : ℝ) = |((N : ℤ) : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    have hcast : ((2 ^ p.f * N.natAbs ^ K : ℕ) : ℝ) / ((bigF p ^ K : ℕ) : ℝ) = 2 ^ p.f * T ^ K := by
      push_cast
      rw [hcastAbs, Even.pow_abs hKeven, ← hNF, div_pow]
      have : ((bigF p : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    have hdiv := natDiv_close (2 ^ p.f * N.natAbs ^ K) (bigF p ^ K) (by positivity)
    rw [hcast] at hdiv
    calc |((2 ^ p.f * N.natAbs ^ K / bigF p ^ K : ℕ) : ℝ) - 2 ^ p.f * Real.exp (x / 2 ^ p.t)|
        = |(((2 ^ p.f * N.natAbs ^ K / bigF p ^ K : ℕ) : ℝ) - 2 ^ p.f * T ^ K)
            + 2 ^ p.f * (T ^ K - Real.exp y ^ K)| := by rw [hexpK]; ring_nf
      _ ≤ |((2 ^ p.f * N.natAbs ^ K / bigF p ^ K : ℕ) : ℝ) - 2 ^ p.f * T ^ K|
            + |2 ^ p.f * (T ^ K - Real.exp y ^ K)| := abs_add_le _ _
      _ ≤ 1 + 2 ^ p.f * (K * tau p.n * (1 + tau p.n) ^ (K - 1)) := by
          refine add_le_add hdiv.le ?_
          rw [abs_mul, abs_of_pos (by positivity)]
          gcongr
      _ = deltaBound p := by unfold deltaBound; rw [hK]; push_cast; ring

/-- The clamp condition of the chosen parameters: `2^32 ≤ exp 24`, from `exp 1 > 2.7182818283`. -/
theorem clamp_chosen : (2 : ℝ) ^ 32 ≤ Real.exp 24 := by
  have h1 : Real.exp 24 = Real.exp 1 ^ 24 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : (2.7182818283 : ℝ) ^ 24 < Real.exp 1 ^ 24 :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have h3 : (2 : ℝ) ^ 32 ≤ (2.7182818283 : ℝ) ^ 24 := by norm_num
  rw [h1]
  linarith

/-- The error bound of the chosen parameters is at most `2`
(the exact value is `1.00698…`, `delta_bound` in `int_transformer.py`). -/
theorem deltaBound_chosen : deltaBound chosen ≤ 2 := by
  unfold deltaBound chosen tau
  simp only [Nat.factorial]
  norm_num

/-- **Theorem B1 at the chosen parameters.** For every integer `x ≤ 0`,
`|expFix chosen x - 2^32 exp (x / 2^32)| ≤ 2`. -/
theorem expFix_close_chosen (x : ℤ) (hx : x ≤ 0) :
    |(expFix chosen x : ℝ) - 2 ^ 32 * Real.exp (x / 2 ^ 32)| ≤ 2 := by
  have h := expFix_close chosen (by decide) (by decide) (by decide) clamp_chosen x hx
  exact h.trans deltaBound_chosen

/-- The in-range value never exceeds `2^f + deltaBound` and is never negative (as a natural
number); the real value `2^f exp(x/2^t)` lies in `(0, 2^f]` for `x ≤ 0`. -/
theorem expFix_le (p : ExpParams) (hn : 0 < p.n) (hm : 0 < p.m) (hR : p.R ≤ 2 ^ p.m)
    (hclamp : (2 : ℝ) ^ p.f ≤ Real.exp p.R) (x : ℤ) (hx : x ≤ 0) :
    (expFix p x : ℝ) ≤ 2 ^ p.f + deltaBound p := by
  have h := expFix_close p hn hm hR hclamp x hx
  have hx' : (x : ℝ) / 2 ^ p.t ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hx) (by positivity)
  have he : Real.exp (x / 2 ^ p.t) ≤ 1 := Real.exp_le_one_iff.2 hx'
  have h2 : (2 : ℝ) ^ p.f * Real.exp (x / 2 ^ p.t) ≤ 2 ^ p.f := by
    calc (2 : ℝ) ^ p.f * Real.exp (x / 2 ^ p.t) ≤ 2 ^ p.f * 1 := by gcongr
      _ = 2 ^ p.f := mul_one _
  rw [abs_le] at h
  linarith [h.2]

theorem realExp_bounds (p : ExpParams) (x : ℤ) (hx : x ≤ 0) :
    0 ≤ (2 : ℝ) ^ p.f * Real.exp (x / 2 ^ p.t) ∧
      (2 : ℝ) ^ p.f * Real.exp (x / 2 ^ p.t) ≤ 2 ^ p.f := by
  have hx' : (x : ℝ) / 2 ^ p.t ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hx) (by positivity)
  have he : Real.exp (x / 2 ^ p.t) ≤ 1 := Real.exp_le_one_iff.2 hx'
  refine ⟨by positivity, ?_⟩
  calc (2 : ℝ) ^ p.f * Real.exp (x / 2 ^ p.t) ≤ 2 ^ p.f * 1 := by gcongr
    _ = 2 ^ p.f := mul_one _

end Transformer

import Mathlib

/-!
# The phase-grid identity (stage 2, part i)

One of Gromov's analytic neurons at frequency `k` with phases `φ₁, φ₂` has weights
`E1[a] = cos(θa + φ₁)`, `E2[b] = cos(θb + φ₂)`, `W2[c] = cos(θc + φ₁ + φ₂)` with `θx = 2πkx/p`, and
contributes `W2[c] (E1[a] + E2[b])²` to the score of answer `c`. Expanding gives nine cosine waves,
eight of which carry a phase `αφ₁ + βφ₂` with `(α, β) ≠ (0, 0)`. Over the grid
`φ₁ ∈ {0, π/2, π, 3π/2}`, `φ₂ ∈ {0, π/2}` (eight neurons) the eight unwanted waves cancel exactly and
the eight neurons together contribute `4 cos(θa + θb − θc)`. `octet` is that identity, for all real
angles; it is a polynomial identity in `cos` and `sin` of the three angles and needs no
`sin² + cos² = 1`.
-/

namespace PhaseGrid
open Real

/-- The eight phase pairs `(j, l)`: `φ₁ = j π/2`, `φ₂ = l π/2`. -/
def grid : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1)]

theorem cos_add_two_quarters (x : ℝ) : cos (x + 2 * (π / 2)) = -cos x := by
  rw [show x + 2 * (π / 2) = x + π by ring, cos_add_pi]

theorem cos_add_three_quarters (x : ℝ) : cos (x + 3 * (π / 2)) = sin x := by
  rw [show x + 3 * (π / 2) = (x + π) + π / 2 by ring, cos_add_pi_div_two, sin_add_pi, neg_neg]

theorem cos_add_four_quarters (x : ℝ) : cos (x + 4 * (π / 2)) = cos x := by
  rw [show x + 4 * (π / 2) = x + 2 * π by ring, cos_add_two_pi]

/-- One octet of neurons at angles `ta, tb, tc`: the eight phase-grid terms sum to one wave. -/
theorem octet (ta tb tc : ℝ) :
    (grid.map fun jl => cos (tc + jl.1 * (π / 2) + jl.2 * (π / 2)) *
      (cos (ta + jl.1 * (π / 2)) + cos (tb + jl.2 * (π / 2))) ^ 2).sum
    = 4 * cos (ta + tb - tc) := by
  have h11 : ∀ x : ℝ, cos (x + 1 * (π / 2) + 1 * (π / 2)) = -cos x := fun x => by
    rw [show x + 1 * (π / 2) + 1 * (π / 2) = x + 2 * (π / 2) by ring, cos_add_two_quarters]
  have h21 : ∀ x : ℝ, cos (x + 2 * (π / 2) + 1 * (π / 2)) = sin x := fun x => by
    rw [show x + 2 * (π / 2) + 1 * (π / 2) = x + 3 * (π / 2) by ring, cos_add_three_quarters]
  have h31 : ∀ x : ℝ, cos (x + 3 * (π / 2) + 1 * (π / 2)) = cos x := fun x => by
    rw [show x + 3 * (π / 2) + 1 * (π / 2) = x + 4 * (π / 2) by ring, cos_add_four_quarters]
  have h1 : ∀ x : ℝ, cos (x + 1 * (π / 2)) = -sin x := fun x => by
    rw [one_mul, cos_add_pi_div_two]
  simp only [grid, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, zero_mul, add_zero, h11, h21, h31, h1, cos_add_two_quarters,
    cos_add_three_quarters]
  rw [cos_sub, cos_add, sin_add]
  ring

end PhaseGrid

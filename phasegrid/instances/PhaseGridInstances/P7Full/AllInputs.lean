import PhaseGridInstances.P7Full.Rows00
import PhaseGridInstances.P7Full.Rows01

/-!
# The phase-grid network at p = 7, frequencies [1, 2, 3], scale M = 25: right on every input

The network answers `(a + b) % 7` for all 49 pairs `(a, b)`.
-/

namespace PhaseGridInstances.P7Full

theorem adds_mod_7 : ∀ a, a < 7 → ∀ b, b < 7 → answer a b = (a + b) % 7 := by
  intro a ha
  match a, ha with
  | 0, _ => exact row_0
  | 1, _ => exact row_1
  | 2, _ => exact row_2
  | 3, _ => exact row_3
  | 4, _ => exact row_4
  | 5, _ => exact row_5
  | 6, _ => exact row_6
  | n + 7, h => exact absurd h (by omega)

end PhaseGridInstances.P7Full

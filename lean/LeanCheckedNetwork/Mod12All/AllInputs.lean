import LeanCheckedNetwork.Mod12All.Rows00
import LeanCheckedNetwork.Mod12All.Rows01
import LeanCheckedNetwork.Mod12All.Rows02
import LeanCheckedNetwork.Mod12All.Rows03

/-!
# Mod12All: right on every input

The network answers `(a + b) % 12` for all 144 pairs `(a, b)`.
-/

namespace LeanCheckedNetwork.Mod12All

theorem adds_mod_12 : ∀ a, a < 12 → ∀ b, b < 12 → answer a b = (a + b) % 12 := by
  intro a ha
  match a, ha with
  | 0, _ => exact row_0
  | 1, _ => exact row_1
  | 2, _ => exact row_2
  | 3, _ => exact row_3
  | 4, _ => exact row_4
  | 5, _ => exact row_5
  | 6, _ => exact row_6
  | 7, _ => exact row_7
  | 8, _ => exact row_8
  | 9, _ => exact row_9
  | 10, _ => exact row_10
  | 11, _ => exact row_11
  | n + 12, h => exact absurd h (by omega)

end LeanCheckedNetwork.Mod12All

import LeanCheckedNetwork.Mod7All.Rows00
import LeanCheckedNetwork.Mod7All.Rows01
import LeanCheckedNetwork.Mod7All.Rows02
import LeanCheckedNetwork.Mod7All.Rows03

/-!
# Mod7All: right on every input

The network answers `(a + b) % 7` for all 49 pairs `(a, b)`.
-/

namespace LeanCheckedNetwork.Mod7All

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

end LeanCheckedNetwork.Mod7All

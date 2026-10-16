```lean
import LeanCheckedNetwork.Weights

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

-- The full statement, but not under the required name.
theorem adds_mod_7_really : ∀ a, a < 7 → ∀ b, b < 7 → answer a b = (a + b) % 7 := by
  decide +kernel

end LeanCheckedNetwork.Net
```

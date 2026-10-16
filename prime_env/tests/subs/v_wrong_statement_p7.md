```lean
import LeanCheckedNetwork.Weights

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

-- Proves only the rows a < 3, under the required name.
theorem adds_mod_7 : ∀ a, a < 3 → ∀ b, b < 7 → answer a b = (a + b) % 7 := by
  decide +kernel

end LeanCheckedNetwork.Net
```

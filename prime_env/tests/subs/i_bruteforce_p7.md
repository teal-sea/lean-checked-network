Small p, so the kernel can evaluate every pair directly.

```lean
import LeanCheckedNetwork.Weights

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

theorem adds_mod_7 : ∀ a, a < 7 → ∀ b, b < 7 → answer a b = (a + b) % 7 := by
  decide +kernel

end LeanCheckedNetwork.Net
```

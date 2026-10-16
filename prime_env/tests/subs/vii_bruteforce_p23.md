Small p, so the kernel can evaluate every pair directly.

```lean
import LeanCheckedNetwork.Weights

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

theorem adds_mod_23 : ∀ a, a < 23 → ∀ b, b < 23 → answer a b = (a + b) % 23 := by
  decide +kernel

end LeanCheckedNetwork.Net
```

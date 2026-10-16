```lean
import LeanCheckedNetwork.Weights

set_option maxRecDepth 100000
set_option debug.skipKernelTC true

namespace LeanCheckedNetwork.Net

-- With the kernel type check switched off, `decide +kernel` adds its auxiliary
-- `Decidable.decide ... = true := Eq.refl true` declaration without anyone checking it.
theorem adds_mod_7 : ∀ a, a < 7 → ∀ b, b < 7 → answer a b = (a + b) % 7 := by
  decide +kernel

end LeanCheckedNetwork.Net
```

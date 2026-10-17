import Transformer.Net.Table

/-! Rows 6 to 6 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

namespace Transformer.Net

open Transformer

/-- Row 6: the packed program answers (6 + b) % 113 with margin above 2E for every b, and its
digit checks pass; `fastCheck_correct` turns this into the statement about the model. -/
theorem fast_6 : ∀ b, b < 113 → fastCheck cfg tab bnd E2 6 b = true := by
  decide +kernel

end Transformer.Net

import Transformer.Net.Table

/-! Rows 55 to 55 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

namespace Transformer.Net

open Transformer

/-- Row 55: the packed program answers (55 + b) % 113 with margin above 2E for every b, and its
digit checks pass; `fastCheck_correct` turns this into the statement about the model. -/
theorem fast_55 : ∀ b, b < 113 → fastCheck cfg tab bnd E2 55 b = true := by
  decide +kernel

end Transformer.Net

import Transformer.Net.Table

/-! Rows 31 to 31 of the addition table, checked by Lean's kernel for all 113 values of `b`. -/

namespace Transformer.Net

open Transformer

/-- Row 31: the packed program answers (31 + b) % 113 with margin above 2E for every b, and its
digit checks pass; `fastCheck_correct` turns this into the statement about the model. -/
theorem fast_31 : ∀ b, b < 113 → fastCheck cfg tab bnd E2 31 b = true := by
  decide +kernel

end Transformer.Net

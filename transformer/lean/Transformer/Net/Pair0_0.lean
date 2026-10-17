import Transformer.Net.Weights

/-! Fixed-pair kernel pilot only. Does not establish fast_0 or all-input acceptance. -/

namespace Transformer.Net

open Transformer

theorem pilot_0_0 : fastCheck cfg tab bnd E2 0 0 = true := by
  decide +kernel

end Transformer.Net

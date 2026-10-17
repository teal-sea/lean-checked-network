import Transformer.Net.Weights

/-! Fixed-pair kernel pilot only. Does not establish fast_0 or all-input acceptance. -/

namespace Transformer.Net

open Transformer

theorem pilot_96_73 : fastCheck cfg tab bnd E2 96 73 = true := by
  decide +kernel

end Transformer.Net

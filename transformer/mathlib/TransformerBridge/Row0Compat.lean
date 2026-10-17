import TransformerBridge.Bridge
import TransformerCore.Net.Weights

namespace TransformerBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem cfg_eq_of_fields (x y : TransformerCore.Cfg)
    (hS : x.S2 = y.S2) (hf : x.f2 = y.f2) (hl : x.lo = y.lo)
    (hp : x.pw = y.pw) (hc : x.cs = y.cs) (hF : x.Fpow = y.Fpow) : x = y := by
  cases x
  cases y
  simp_all

theorem row0_cfg : cfgOf Transformer.chosen 256 = TransformerCore.Net.cfg := by
  apply cfg_eq_of_fields <;> decide +kernel

theorem row0_E2 : (TransformerCore.Net.E2 : ℤ) =
    2 * (Transformer.Ebound 256 Transformer.chosen.f 2 Transformer.chosenBounds : ℤ) := by
  change (TransformerCore.Net.E2 : ℤ) =
    2 * (Transformer.Ebound 256 32 2 Transformer.chosenBounds : ℤ)
  rw [Transformer.Ebound_chosen]
  decide +kernel

end TransformerBridge

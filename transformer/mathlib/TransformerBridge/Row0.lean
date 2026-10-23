import TransformerBridge.Row0Checks
import TransformerBridge.Row0Compat
import TransformerCore.Net.Table
import TransformerCore.Net.Cols

namespace TransformerBridge

/-- Integer margin on exactly the first row of the frozen fused quantized tables. -/
theorem row0_integer_margin (b : Fin 113) (k : Fin 113) (hk : k ≠ Transformer.ans 0 b) :
    Transformer.intLogits Transformer.chosen (toTables TransformerCore.Net.tab) 256 0 b k
      + 2 * (Transformer.Ebound 256 Transformer.chosen.f 2 Transformer.chosenBounds : ℤ)
      < Transformer.intLogits Transformer.chosen (toTables TransformerCore.Net.tab) 256 0 b
          (Transformer.ans 0 b) := by
  have hf := row0_fastCheck b
  rw [← row0_cfg] at hf
  have hm := hA_of_fastCheck Transformer.chosen 256 TransformerCore.Net.tab
    TransformerCore.Net.bnd TransformerCore.Net.E2 TransformerCore.Net.tables_ok
    TransformerCore.Net.G_length 0 b hf k hk
  rw [row0_E2] at hm
  exact hm

end TransformerBridge

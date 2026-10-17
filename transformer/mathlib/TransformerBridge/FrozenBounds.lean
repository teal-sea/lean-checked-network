import TransformerBridge.Bounds
import TransformerCore.Net.Table
import TransformerCore.Net.Cols

namespace TransformerBridge

/-- Unconditional bound for the exact frozen table, with the original chosen bounds. -/
theorem frozen_tables_bounded :
    (toTables TransformerCore.Net.tab).Bounded Transformer.chosenBounds := by
  apply bounded_of_core TransformerCore.Net.tab TransformerCore.Net.bnd Transformer.chosenBounds
    TransformerCore.Net.tables_ok TransformerCore.Net.G_length
  · intro h; fin_cases h <;> norm_num [TransformerCore.Net.bnd, Transformer.chosenBounds]
  · intro h; fin_cases h <;> norm_num [TransformerCore.Net.bnd, Transformer.chosenBounds]
  · norm_num [TransformerCore.Net.bnd, Transformer.chosenBounds]
  · norm_num [TransformerCore.Net.bnd, Transformer.chosenBounds]
  · exact TransformerCore.Net.colSums_ok

end TransformerBridge

import Transformer.Fast
import Transformer.Net.Weights

namespace Transformer.Net

/-- Every table has the right shape and its entries are within `bnd`: the one-time check the fast
evaluator's proof needs. -/
theorem tables_ok : tablesOk tab bnd = true := by decide +kernel

end Transformer.Net

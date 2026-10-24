import ACASChecked.N29.NodeDataNC
namespace Proof29
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem claims_length : Leaf29.claims.length = 501 := by decide +kernel
#print axioms claims_length
end Proof29

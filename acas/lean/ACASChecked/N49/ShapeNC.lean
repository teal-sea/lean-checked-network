import ACASChecked.N49.NodeDataNC
namespace Proof49
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem claims_length : Leaf49.claims.length = 501 := by decide +kernel
#print axioms claims_length
end Proof49

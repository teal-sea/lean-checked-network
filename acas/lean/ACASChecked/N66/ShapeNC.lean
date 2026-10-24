import ACASChecked.N66.NodeDataNC
namespace Proof66
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem claims_length : Leaf66.claims.length = 501 := by decide +kernel
#print axioms claims_length
end Proof66

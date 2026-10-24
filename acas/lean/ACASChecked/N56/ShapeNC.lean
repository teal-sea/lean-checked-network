import ACASChecked.N56.NodeDataNC
namespace Proof56
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem claims_length : Leaf56.claims.length = 501 := by decide +kernel
#print axioms claims_length
end Proof56

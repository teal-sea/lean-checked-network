import ACASChecked.N54.NodeDataNC
namespace Proof54
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem claims_length : Leaf54.claims.length = 501 := by decide +kernel
#print axioms claims_length
end Proof54

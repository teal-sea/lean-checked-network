import ACASChecked.N37.NodeDataNC
namespace Proof37
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem claims_length : Leaf37.claims.length = 501 := by decide +kernel
#print axioms claims_length
end Proof37

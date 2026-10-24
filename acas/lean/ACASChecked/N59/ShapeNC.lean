import ACASChecked.N59.NodeDataNC
namespace Proof59
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem claims_length : Leaf59.claims.length = 501 := by decide +kernel
#print axioms claims_length
end Proof59

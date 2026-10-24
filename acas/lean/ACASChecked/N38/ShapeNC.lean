import ACASChecked.N38.NodeDataNC
namespace Proof38
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem claims_length : Leaf38.claims.length = 501 := by decide +kernel
#print axioms claims_length
end Proof38

import ACASChecked.N42.NodeDataNC
namespace Proof42
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem claims_length : Leaf42.claims.length = 501 := by decide +kernel
#print axioms claims_length
end Proof42

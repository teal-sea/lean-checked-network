import ACASChecked.N39.NodeDataNC
namespace Proof39
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem claims_length : Leaf39.claims.length = 501 := by decide +kernel
#print axioms claims_length
end Proof39

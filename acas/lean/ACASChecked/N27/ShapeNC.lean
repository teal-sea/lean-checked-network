import ACASChecked.N27.NodeDataNC
namespace Proof27
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem claims_length : Leaf27.claims.length = 501 := by decide +kernel
#print axioms claims_length
end Proof27

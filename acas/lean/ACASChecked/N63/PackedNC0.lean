import ACASChecked.N63.DataNC0
namespace Proof63
open SharedWeights
open RouteA Leaf63
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem packedNC0 : block w0 v0 c0 = true := by decide +kernel
#print axioms packedNC0
end Proof63

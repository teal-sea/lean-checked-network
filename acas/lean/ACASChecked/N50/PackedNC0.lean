import ACASChecked.N50.DataNC0
namespace Proof50
open SharedWeights
open RouteA Leaf50
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem packedNC0 : block w0 v0 c0 = true := by decide +kernel
#print axioms packedNC0
end Proof50

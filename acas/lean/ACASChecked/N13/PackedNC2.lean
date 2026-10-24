import ACASChecked.N13.DataNC2
namespace Proof13
open SharedWeights
open RouteA Leaf13
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem packedNC2 : block w2 v2 c2 = true := by decide +kernel
#print axioms packedNC2
end Proof13

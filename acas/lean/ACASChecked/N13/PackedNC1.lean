import ACASChecked.N13.DataNC1
namespace Proof13
open SharedWeights
open RouteA Leaf13
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem packedNC1 : block w1 v1 c1 = true := by decide +kernel
#print axioms packedNC1
end Proof13

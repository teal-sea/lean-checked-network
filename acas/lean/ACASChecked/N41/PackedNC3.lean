import ACASChecked.N41.DataNC3
namespace Proof41
open SharedWeights
open RouteA Leaf41
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem packedNC3 : block w3 v3 c3 = true := by decide +kernel
#print axioms packedNC3
end Proof41

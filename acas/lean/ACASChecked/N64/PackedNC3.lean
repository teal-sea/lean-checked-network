import ACASChecked.N64.DataNC3
namespace Proof64
open SharedWeights
open RouteA Leaf64
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem packedNC3 : block w3 v3 c3 = true := by decide +kernel
#print axioms packedNC3
end Proof64

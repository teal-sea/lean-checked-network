import ACASChecked.N65.DataNC5
namespace Proof65
open SharedWeights
open RouteA Leaf65
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem packedNC5 : block w5 v5 c5 = true := by decide +kernel
#print axioms packedNC5
end Proof65

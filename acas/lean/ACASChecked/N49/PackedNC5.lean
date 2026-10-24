import ACASChecked.N49.DataNC5
namespace Proof49
open SharedWeights
open RouteA Leaf49
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem packedNC5 : block w5 v5 c5 = true := by decide +kernel
#print axioms packedNC5
end Proof49

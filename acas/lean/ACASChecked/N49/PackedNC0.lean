import ACASChecked.N49.DataNC0
namespace Proof49
open SharedWeights
open RouteA Leaf49
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem packedNC0 : block w0 v0 c0 = true := by decide +kernel
#print axioms packedNC0
end Proof49

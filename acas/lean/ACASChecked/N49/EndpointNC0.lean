import ACASChecked.N49.NodeDataNC
namespace Proof49
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC0 : Leaf49.endpoints0 = true := by decide +kernel
#print axioms endpointsNC0
end Proof49

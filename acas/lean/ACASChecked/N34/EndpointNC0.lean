import ACASChecked.N34.NodeDataNC
namespace Proof34
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC0 : Leaf34.endpoints0 = true := by decide +kernel
#print axioms endpointsNC0
end Proof34

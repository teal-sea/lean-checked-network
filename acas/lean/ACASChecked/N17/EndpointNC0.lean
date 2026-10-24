import ACASChecked.N17.NodeDataNC
namespace Proof17
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC0 : Leaf17.endpoints0 = true := by decide +kernel
#print axioms endpointsNC0
end Proof17

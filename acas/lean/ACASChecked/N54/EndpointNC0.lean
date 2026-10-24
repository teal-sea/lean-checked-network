import ACASChecked.N54.NodeDataNC
namespace Proof54
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC0 : Leaf54.endpoints0 = true := by decide +kernel
#print axioms endpointsNC0
end Proof54

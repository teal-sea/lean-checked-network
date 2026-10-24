import ACASChecked.N31.NodeDataNC
namespace Proof31
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC0 : Leaf31.endpoints0 = true := by decide +kernel
#print axioms endpointsNC0
end Proof31

import ACASChecked.N66.NodeDataNC
namespace Proof66
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC0 : Leaf66.endpoints0 = true := by decide +kernel
#print axioms endpointsNC0
end Proof66

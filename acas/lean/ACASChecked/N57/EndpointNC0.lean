import ACASChecked.N57.NodeDataNC
namespace Proof57
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC0 : Leaf57.endpoints0 = true := by decide +kernel
#print axioms endpointsNC0
end Proof57

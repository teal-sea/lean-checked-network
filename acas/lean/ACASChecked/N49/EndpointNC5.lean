import ACASChecked.N49.ChunkNC4
namespace Proof49
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC5 : Leaf49.endpoints5 = true := by
 unfold Leaf49.endpoints5
 rw [chunk4]
 decide +kernel
#print axioms endpointsNC5
end Proof49

import ACASChecked.N49.ChunkNC3
namespace Proof49
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC4 : Leaf49.endpoints4 = true := by
 unfold Leaf49.endpoints4
 rw [chunk3]
 decide +kernel
#print axioms endpointsNC4
end Proof49

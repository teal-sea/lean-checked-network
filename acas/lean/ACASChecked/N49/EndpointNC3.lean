import ACASChecked.N49.ChunkNC2
namespace Proof49
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC3 : Leaf49.endpoints3 = true := by
 unfold Leaf49.endpoints3
 rw [chunk2]
 decide +kernel
#print axioms endpointsNC3
end Proof49

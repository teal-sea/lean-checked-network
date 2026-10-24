import ACASChecked.N49.ChunkNC1
namespace Proof49
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC2 : Leaf49.endpoints2 = true := by
 unfold Leaf49.endpoints2
 rw [chunk1]
 decide +kernel
#print axioms endpointsNC2
end Proof49

import ACASChecked.N33.ChunkNC1
namespace Proof33
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC2 : Leaf33.endpoints2 = true := by
 unfold Leaf33.endpoints2
 rw [chunk1]
 decide +kernel
#print axioms endpointsNC2
end Proof33

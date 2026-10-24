import ACASChecked.N33.ChunkNC2
namespace Proof33
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC3 : Leaf33.endpoints3 = true := by
 unfold Leaf33.endpoints3
 rw [chunk2]
 decide +kernel
#print axioms endpointsNC3
end Proof33

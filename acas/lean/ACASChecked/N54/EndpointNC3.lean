import ACASChecked.N54.ChunkNC2
namespace Proof54
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC3 : Leaf54.endpoints3 = true := by
 unfold Leaf54.endpoints3
 rw [chunk2]
 decide +kernel
#print axioms endpointsNC3
end Proof54

import ACASChecked.N64.ChunkNC2
namespace Proof64
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC3 : Leaf64.endpoints3 = true := by
 unfold Leaf64.endpoints3
 rw [chunk2]
 decide +kernel
#print axioms endpointsNC3
end Proof64

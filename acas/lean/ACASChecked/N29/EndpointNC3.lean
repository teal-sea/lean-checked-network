import ACASChecked.N29.ChunkNC2
namespace Proof29
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC3 : Leaf29.endpoints3 = true := by
 unfold Leaf29.endpoints3
 rw [chunk2]
 decide +kernel
#print axioms endpointsNC3
end Proof29

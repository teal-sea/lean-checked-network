import ACASChecked.N32.ChunkNC2
namespace Proof32
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC3 : Leaf32.endpoints3 = true := by
 unfold Leaf32.endpoints3
 rw [chunk2]
 decide +kernel
#print axioms endpointsNC3
end Proof32

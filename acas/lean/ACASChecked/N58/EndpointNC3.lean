import ACASChecked.N58.ChunkNC2
namespace Proof58
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC3 : Leaf58.endpoints3 = true := by
 unfold Leaf58.endpoints3
 rw [chunk2]
 decide +kernel
#print axioms endpointsNC3
end Proof58

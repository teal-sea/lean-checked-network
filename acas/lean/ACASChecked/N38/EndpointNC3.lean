import ACASChecked.N38.ChunkNC2
namespace Proof38
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC3 : Leaf38.endpoints3 = true := by
 unfold Leaf38.endpoints3
 rw [chunk2]
 decide +kernel
#print axioms endpointsNC3
end Proof38

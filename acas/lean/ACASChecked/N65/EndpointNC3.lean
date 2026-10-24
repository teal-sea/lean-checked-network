import ACASChecked.N65.ChunkNC2
namespace Proof65
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC3 : Leaf65.endpoints3 = true := by
 unfold Leaf65.endpoints3
 rw [chunk2]
 decide +kernel
#print axioms endpointsNC3
end Proof65

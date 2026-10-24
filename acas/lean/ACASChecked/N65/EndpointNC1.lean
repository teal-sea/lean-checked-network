import ACASChecked.N65.ChunkNC0
namespace Proof65
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC1 : Leaf65.endpoints1 = true := by
 unfold Leaf65.endpoints1
 rw [chunk0]
 decide +kernel
#print axioms endpointsNC1
end Proof65

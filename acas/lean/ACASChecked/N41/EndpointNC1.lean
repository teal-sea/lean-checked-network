import ACASChecked.N41.ChunkNC0
namespace Proof41
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC1 : Leaf41.endpoints1 = true := by
 unfold Leaf41.endpoints1
 rw [chunk0]
 decide +kernel
#print axioms endpointsNC1
end Proof41

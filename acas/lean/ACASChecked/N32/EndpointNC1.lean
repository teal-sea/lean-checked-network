import ACASChecked.N32.ChunkNC0
namespace Proof32
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC1 : Leaf32.endpoints1 = true := by
 unfold Leaf32.endpoints1
 rw [chunk0]
 decide +kernel
#print axioms endpointsNC1
end Proof32

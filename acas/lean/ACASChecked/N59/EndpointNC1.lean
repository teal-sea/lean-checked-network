import ACASChecked.N59.ChunkNC0
namespace Proof59
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC1 : Leaf59.endpoints1 = true := by
 unfold Leaf59.endpoints1
 rw [chunk0]
 decide +kernel
#print axioms endpointsNC1
end Proof59

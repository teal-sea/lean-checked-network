import ACASChecked.N59.ChunkNC3
namespace Proof59
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC4 : Leaf59.endpoints4 = true := by
 unfold Leaf59.endpoints4
 rw [chunk3]
 decide +kernel
#print axioms endpointsNC4
end Proof59

import ACASChecked.N59.ChunkNC1
namespace Proof59
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC2 : Leaf59.endpoints2 = true := by
 unfold Leaf59.endpoints2
 rw [chunk1]
 decide +kernel
#print axioms endpointsNC2
end Proof59

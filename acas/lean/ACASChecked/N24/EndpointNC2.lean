import ACASChecked.N24.ChunkNC1
namespace Proof24
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC2 : Leaf24.endpoints2 = true := by
 unfold Leaf24.endpoints2
 rw [chunk1]
 decide +kernel
#print axioms endpointsNC2
end Proof24

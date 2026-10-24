import ACASChecked.N29.ChunkNC1
namespace Proof29
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC2 : Leaf29.endpoints2 = true := by
 unfold Leaf29.endpoints2
 rw [chunk1]
 decide +kernel
#print axioms endpointsNC2
end Proof29

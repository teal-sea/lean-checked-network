import ACASChecked.N52.ChunkNC1
namespace Proof52
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC2 : Leaf52.endpoints2 = true := by
 unfold Leaf52.endpoints2
 rw [chunk1]
 decide +kernel
#print axioms endpointsNC2
end Proof52

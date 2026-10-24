import ACASChecked.N50.ChunkNC1
namespace Proof50
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC2 : Leaf50.endpoints2 = true := by
 unfold Leaf50.endpoints2
 rw [chunk1]
 decide +kernel
#print axioms endpointsNC2
end Proof50

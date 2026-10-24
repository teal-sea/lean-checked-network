import ACASChecked.N63.ChunkNC2
namespace Proof63
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC3 : Leaf63.endpoints3 = true := by
 unfold Leaf63.endpoints3
 rw [chunk2]
 decide +kernel
#print axioms endpointsNC3
end Proof63

import ACASChecked.N17.ChunkNC2
namespace Proof17
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC3 : Leaf17.endpoints3 = true := by
 unfold Leaf17.endpoints3
 rw [chunk2]
 decide +kernel
#print axioms endpointsNC3
end Proof17

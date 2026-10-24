import ACASChecked.N30.ChunkNC2
namespace Proof30
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC3 : Leaf30.endpoints3 = true := by
 unfold Leaf30.endpoints3
 rw [chunk2]
 decide +kernel
#print axioms endpointsNC3
end Proof30

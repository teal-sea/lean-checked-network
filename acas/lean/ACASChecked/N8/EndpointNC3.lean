import ACASChecked.N8.ChunkNC2
namespace Proof8
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC3 : Leaf8.endpoints3 = true := by
 unfold Leaf8.endpoints3
 rw [chunk2]
 decide +kernel
#print axioms endpointsNC3
end Proof8

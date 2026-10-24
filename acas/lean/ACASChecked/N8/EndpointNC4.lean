import ACASChecked.N8.ChunkNC3
namespace Proof8
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC4 : Leaf8.endpoints4 = true := by
 unfold Leaf8.endpoints4
 rw [chunk3]
 decide +kernel
#print axioms endpointsNC4
end Proof8

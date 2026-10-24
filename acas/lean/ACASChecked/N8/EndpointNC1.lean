import ACASChecked.N8.ChunkNC0
namespace Proof8
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC1 : Leaf8.endpoints1 = true := by
 unfold Leaf8.endpoints1
 rw [chunk0]
 decide +kernel
#print axioms endpointsNC1
end Proof8

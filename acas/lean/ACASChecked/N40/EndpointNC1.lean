import ACASChecked.N40.ChunkNC0
namespace Proof40
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC1 : Leaf40.endpoints1 = true := by
 unfold Leaf40.endpoints1
 rw [chunk0]
 decide +kernel
#print axioms endpointsNC1
end Proof40

import ACASChecked.N40.ChunkNC3
namespace Proof40
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC4 : Leaf40.endpoints4 = true := by
 unfold Leaf40.endpoints4
 rw [chunk3]
 decide +kernel
#print axioms endpointsNC4
end Proof40

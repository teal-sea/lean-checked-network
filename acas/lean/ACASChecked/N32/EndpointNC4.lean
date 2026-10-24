import ACASChecked.N32.ChunkNC3
namespace Proof32
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC4 : Leaf32.endpoints4 = true := by
 unfold Leaf32.endpoints4
 rw [chunk3]
 decide +kernel
#print axioms endpointsNC4
end Proof32

import ACASChecked.N50.ChunkNC3
namespace Proof50
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC4 : Leaf50.endpoints4 = true := by
 unfold Leaf50.endpoints4
 rw [chunk3]
 decide +kernel
#print axioms endpointsNC4
end Proof50

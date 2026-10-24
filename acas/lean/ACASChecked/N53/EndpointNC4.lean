import ACASChecked.N53.ChunkNC3
namespace Proof53
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC4 : Leaf53.endpoints4 = true := by
 unfold Leaf53.endpoints4
 rw [chunk3]
 decide +kernel
#print axioms endpointsNC4
end Proof53

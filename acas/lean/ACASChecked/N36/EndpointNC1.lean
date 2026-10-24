import ACASChecked.N36.ChunkNC0
namespace Proof36
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC1 : Leaf36.endpoints1 = true := by
 unfold Leaf36.endpoints1
 rw [chunk0]
 decide +kernel
#print axioms endpointsNC1
end Proof36

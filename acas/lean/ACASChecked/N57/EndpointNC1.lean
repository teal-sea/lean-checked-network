import ACASChecked.N57.ChunkNC0
namespace Proof57
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC1 : Leaf57.endpoints1 = true := by
 unfold Leaf57.endpoints1
 rw [chunk0]
 decide +kernel
#print axioms endpointsNC1
end Proof57

import ACASChecked.N13.ChunkNC0
namespace Proof13
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC1 : Leaf13.endpoints1 = true := by
 unfold Leaf13.endpoints1
 rw [chunk0]
 decide +kernel
#print axioms endpointsNC1
end Proof13

import ACASChecked.N13.ChunkNC4
namespace Proof13
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC5 : Leaf13.endpoints5 = true := by
 unfold Leaf13.endpoints5
 rw [chunk4]
 decide +kernel
#print axioms endpointsNC5
end Proof13

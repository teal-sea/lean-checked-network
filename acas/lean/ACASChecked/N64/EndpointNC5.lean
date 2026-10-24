import ACASChecked.N64.ChunkNC4
namespace Proof64
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC5 : Leaf64.endpoints5 = true := by
 unfold Leaf64.endpoints5
 rw [chunk4]
 decide +kernel
#print axioms endpointsNC5
end Proof64

import ACASChecked.N24.ChunkNC4
namespace Proof24
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC5 : Leaf24.endpoints5 = true := by
 unfold Leaf24.endpoints5
 rw [chunk4]
 decide +kernel
#print axioms endpointsNC5
end Proof24

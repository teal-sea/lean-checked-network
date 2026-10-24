import ACASChecked.N38.ChunkNC4
namespace Proof38
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC5 : Leaf38.endpoints5 = true := by
 unfold Leaf38.endpoints5
 rw [chunk4]
 decide +kernel
#print axioms endpointsNC5
end Proof38

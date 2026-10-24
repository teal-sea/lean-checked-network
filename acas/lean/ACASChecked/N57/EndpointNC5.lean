import ACASChecked.N57.ChunkNC4
namespace Proof57
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC5 : Leaf57.endpoints5 = true := by
 unfold Leaf57.endpoints5
 rw [chunk4]
 decide +kernel
#print axioms endpointsNC5
end Proof57

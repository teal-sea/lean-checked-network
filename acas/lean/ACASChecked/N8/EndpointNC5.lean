import ACASChecked.N8.ChunkNC4
namespace Proof8
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC5 : Leaf8.endpoints5 = true := by
 unfold Leaf8.endpoints5
 rw [chunk4]
 decide +kernel
#print axioms endpointsNC5
end Proof8

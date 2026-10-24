import ACASChecked.N46.ChunkNC4
namespace Proof46
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC5 : Leaf46.endpoints5 = true := by
 unfold Leaf46.endpoints5
 rw [chunk4]
 decide +kernel
#print axioms endpointsNC5
end Proof46

import ACASChecked.N39.ChunkNC4
namespace Proof39
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC5 : Leaf39.endpoints5 = true := by
 unfold Leaf39.endpoints5
 rw [chunk4]
 decide +kernel
#print axioms endpointsNC5
end Proof39

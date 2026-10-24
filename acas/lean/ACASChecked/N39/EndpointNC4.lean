import ACASChecked.N39.ChunkNC3
namespace Proof39
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC4 : Leaf39.endpoints4 = true := by
 unfold Leaf39.endpoints4
 rw [chunk3]
 decide +kernel
#print axioms endpointsNC4
end Proof39

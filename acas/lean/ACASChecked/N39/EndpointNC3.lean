import ACASChecked.N39.ChunkNC2
namespace Proof39
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC3 : Leaf39.endpoints3 = true := by
 unfold Leaf39.endpoints3
 rw [chunk2]
 decide +kernel
#print axioms endpointsNC3
end Proof39

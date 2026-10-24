import ACASChecked.N57.ChunkNC2
namespace Proof57
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC3 : Leaf57.endpoints3 = true := by
 unfold Leaf57.endpoints3
 rw [chunk2]
 decide +kernel
#print axioms endpointsNC3
end Proof57

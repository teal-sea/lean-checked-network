import ACASChecked.N30.ChunkNC1
namespace Proof30
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC2 : Leaf30.endpoints2 = true := by
 unfold Leaf30.endpoints2
 rw [chunk1]
 decide +kernel
#print axioms endpointsNC2
end Proof30

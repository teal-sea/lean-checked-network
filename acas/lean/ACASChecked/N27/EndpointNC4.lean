import ACASChecked.N27.ChunkNC3
namespace Proof27
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC4 : Leaf27.endpoints4 = true := by
 unfold Leaf27.endpoints4
 rw [chunk3]
 decide +kernel
#print axioms endpointsNC4
end Proof27

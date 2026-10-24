import ACASChecked.N31.ChunkNC3
namespace Proof31
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem endpointsNC4 : Leaf31.endpoints4 = true := by
 unfold Leaf31.endpoints4
 rw [chunk3]
 decide +kernel
#print axioms endpointsNC4
end Proof31

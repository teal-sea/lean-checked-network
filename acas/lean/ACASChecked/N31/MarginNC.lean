import ACASChecked.N31.ChunkNC5
namespace Proof31
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf31.marginCheck = true := by
 unfold Leaf31.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof31

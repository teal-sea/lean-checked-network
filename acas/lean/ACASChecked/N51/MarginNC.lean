import ACASChecked.N51.ChunkNC5
namespace Proof51
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf51.marginCheck = true := by
 unfold Leaf51.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof51

import ACASChecked.N58.ChunkNC5
namespace Proof58
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf58.marginCheck = true := by
 unfold Leaf58.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof58

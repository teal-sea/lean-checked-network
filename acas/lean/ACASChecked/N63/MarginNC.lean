import ACASChecked.N63.ChunkNC5
namespace Proof63
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf63.marginCheck = true := by
 unfold Leaf63.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof63

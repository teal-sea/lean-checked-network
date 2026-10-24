import ACASChecked.N54.ChunkNC5
namespace Proof54
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf54.marginCheck = true := by
 unfold Leaf54.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof54

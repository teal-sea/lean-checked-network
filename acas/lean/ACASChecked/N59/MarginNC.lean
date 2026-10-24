import ACASChecked.N59.ChunkNC5
namespace Proof59
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf59.marginCheck = true := by
 unfold Leaf59.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof59

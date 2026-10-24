import ACASChecked.N38.ChunkNC5
namespace Proof38
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf38.marginCheck = true := by
 unfold Leaf38.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof38

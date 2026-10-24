import ACASChecked.N65.ChunkNC5
namespace Proof65
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf65.marginCheck = true := by
 unfold Leaf65.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof65

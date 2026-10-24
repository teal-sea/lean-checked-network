import ACASChecked.N41.ChunkNC5
namespace Proof41
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf41.marginCheck = true := by
 unfold Leaf41.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof41

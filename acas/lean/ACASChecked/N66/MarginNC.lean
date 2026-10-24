import ACASChecked.N66.ChunkNC5
namespace Proof66
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf66.marginCheck = true := by
 unfold Leaf66.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof66

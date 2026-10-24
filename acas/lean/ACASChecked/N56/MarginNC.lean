import ACASChecked.N56.ChunkNC5
namespace Proof56
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf56.marginCheck = true := by
 unfold Leaf56.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof56

import ACASChecked.N50.ChunkNC5
namespace Proof50
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf50.marginCheck = true := by
 unfold Leaf50.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof50

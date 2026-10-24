import ACASChecked.N49.ChunkNC5
namespace Proof49
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf49.marginCheck = true := by
 unfold Leaf49.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof49

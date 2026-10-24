import ACASChecked.N34.ChunkNC5
namespace Proof34
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf34.marginCheck = true := by
 unfold Leaf34.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof34

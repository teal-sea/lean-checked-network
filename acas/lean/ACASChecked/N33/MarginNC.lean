import ACASChecked.N33.ChunkNC5
namespace Proof33
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf33.marginCheck = true := by
 unfold Leaf33.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof33

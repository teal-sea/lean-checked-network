import ACASChecked.N17.ChunkNC5
namespace Proof17
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf17.marginCheck = true := by
 unfold Leaf17.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof17

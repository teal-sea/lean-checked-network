import ACASChecked.N30.ChunkNC5
namespace Proof30
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf30.marginCheck = true := by
 unfold Leaf30.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof30

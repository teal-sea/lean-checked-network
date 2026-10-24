import ACASChecked.N36.ChunkNC5
namespace Proof36
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf36.marginCheck = true := by
 unfold Leaf36.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof36

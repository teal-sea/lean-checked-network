import ACASChecked.N24.ChunkNC5
namespace Proof24
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf24.marginCheck = true := by
 unfold Leaf24.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof24

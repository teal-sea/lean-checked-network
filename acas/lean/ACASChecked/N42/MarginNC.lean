import ACASChecked.N42.ChunkNC5
namespace Proof42
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf42.marginCheck = true := by
 unfold Leaf42.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof42

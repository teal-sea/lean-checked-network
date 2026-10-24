import ACASChecked.N37.ChunkNC5
namespace Proof37
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf37.marginCheck = true := by
 unfold Leaf37.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof37

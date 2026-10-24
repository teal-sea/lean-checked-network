import ACASChecked.N55.ChunkNC5
namespace Proof55
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf55.marginCheck = true := by
 unfold Leaf55.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof55

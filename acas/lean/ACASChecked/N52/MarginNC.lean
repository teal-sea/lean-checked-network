import ACASChecked.N52.ChunkNC5
namespace Proof52
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf52.marginCheck = true := by
 unfold Leaf52.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof52

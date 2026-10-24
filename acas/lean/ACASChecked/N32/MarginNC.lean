import ACASChecked.N32.ChunkNC5
namespace Proof32
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf32.marginCheck = true := by
 unfold Leaf32.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof32

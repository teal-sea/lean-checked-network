import ACASChecked.N40.ChunkNC5
namespace Proof40
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf40.marginCheck = true := by
 unfold Leaf40.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof40

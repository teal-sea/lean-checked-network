import ACASChecked.N8.ChunkNC5
namespace Proof8
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf8.marginCheck = true := by
 unfold Leaf8.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof8

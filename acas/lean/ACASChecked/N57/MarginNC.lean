import ACASChecked.N57.ChunkNC5
namespace Proof57
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf57.marginCheck = true := by
 unfold Leaf57.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof57

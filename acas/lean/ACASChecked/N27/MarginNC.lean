import ACASChecked.N27.ChunkNC5
namespace Proof27
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf27.marginCheck = true := by
 unfold Leaf27.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof27

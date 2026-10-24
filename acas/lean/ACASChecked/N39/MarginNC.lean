import ACASChecked.N39.ChunkNC5
namespace Proof39
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf39.marginCheck = true := by
 unfold Leaf39.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof39

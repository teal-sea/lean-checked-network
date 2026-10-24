import ACASChecked.N46.ChunkNC5
namespace Proof46
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf46.marginCheck = true := by
 unfold Leaf46.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof46

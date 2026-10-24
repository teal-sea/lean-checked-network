import ACASChecked.N53.ChunkNC5
namespace Proof53
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem marginNC : Leaf53.marginCheck = true := by
 unfold Leaf53.marginCheck
 rw [chunk5]
 decide +kernel
#print axioms marginNC
end Proof53

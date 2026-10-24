import ACASChecked.N50.DataNC1
namespace Proof50
open SharedWeights
open RouteA Leaf50
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem packedNC1 : block w1 v1 c1 = true := by decide +kernel
#print axioms packedNC1
end Proof50

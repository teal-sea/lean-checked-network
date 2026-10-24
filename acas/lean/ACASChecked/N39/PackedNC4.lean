import ACASChecked.N39.DataNC4
namespace Proof39
open SharedWeights
open RouteA Leaf39
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem packedNC4 : block w4 v4 c4 = true := by decide +kernel
#print axioms packedNC4
end Proof39

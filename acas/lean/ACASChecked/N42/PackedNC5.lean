import ACASChecked.N42.DataNC5
namespace Proof42
open SharedWeights
open RouteA Leaf42
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem packedNC5 : block w5 v5 c5 = true := by decide +kernel
#print axioms packedNC5
end Proof42

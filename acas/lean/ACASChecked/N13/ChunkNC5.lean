import ACASChecked.N13.NodeDataNC
import ACASChecked.SameSpec
namespace Proof13
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool5 : RouteA.same ((Leaf13.claims.drop 500).take 1) ((Leaf13.supplied.drop 500).take 1) = true := by decide +kernel
theorem chunk5 : (Leaf13.claims.drop 500).take 1 = (Leaf13.supplied.drop 500).take 1 := RouteA.same_spec _ _ chunkBool5
#print axioms chunk5
end Proof13

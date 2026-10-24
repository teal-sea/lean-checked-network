import ACASChecked.N55.NodeDataNC
import ACASChecked.SameSpec
namespace Proof55
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool5 : RouteA.same ((Leaf55.claims.drop 500).take 1) ((Leaf55.supplied.drop 500).take 1) = true := by decide +kernel
theorem chunk5 : (Leaf55.claims.drop 500).take 1 = (Leaf55.supplied.drop 500).take 1 := RouteA.same_spec _ _ chunkBool5
#print axioms chunk5
end Proof55

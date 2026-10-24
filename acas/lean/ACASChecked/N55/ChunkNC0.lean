import ACASChecked.N55.NodeDataNC
import ACASChecked.SameSpec
namespace Proof55
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool0 : RouteA.same ((Leaf55.claims.drop 0).take 100) ((Leaf55.supplied.drop 0).take 100) = true := by decide +kernel
theorem chunk0 : (Leaf55.claims.drop 0).take 100 = (Leaf55.supplied.drop 0).take 100 := RouteA.same_spec _ _ chunkBool0
#print axioms chunk0
end Proof55

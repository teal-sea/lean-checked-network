import ACASChecked.N52.NodeDataNC
import ACASChecked.SameSpec
namespace Proof52
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool4 : RouteA.same ((Leaf52.claims.drop 400).take 100) ((Leaf52.supplied.drop 400).take 100) = true := by decide +kernel
theorem chunk4 : (Leaf52.claims.drop 400).take 100 = (Leaf52.supplied.drop 400).take 100 := RouteA.same_spec _ _ chunkBool4
#print axioms chunk4
end Proof52

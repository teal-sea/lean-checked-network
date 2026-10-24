import ACASChecked.N64.NodeDataNC
import ACASChecked.SameSpec
namespace Proof64
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool4 : RouteA.same ((Leaf64.claims.drop 400).take 100) ((Leaf64.supplied.drop 400).take 100) = true := by decide +kernel
theorem chunk4 : (Leaf64.claims.drop 400).take 100 = (Leaf64.supplied.drop 400).take 100 := RouteA.same_spec _ _ chunkBool4
#print axioms chunk4
end Proof64

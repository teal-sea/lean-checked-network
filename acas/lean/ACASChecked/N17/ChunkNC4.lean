import ACASChecked.N17.NodeDataNC
import ACASChecked.SameSpec
namespace Proof17
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool4 : RouteA.same ((Leaf17.claims.drop 400).take 100) ((Leaf17.supplied.drop 400).take 100) = true := by decide +kernel
theorem chunk4 : (Leaf17.claims.drop 400).take 100 = (Leaf17.supplied.drop 400).take 100 := RouteA.same_spec _ _ chunkBool4
#print axioms chunk4
end Proof17

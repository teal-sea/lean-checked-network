import ACASChecked.N54.NodeDataNC
import ACASChecked.SameSpec
namespace Proof54
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool0 : RouteA.same ((Leaf54.claims.drop 0).take 100) ((Leaf54.supplied.drop 0).take 100) = true := by decide +kernel
theorem chunk0 : (Leaf54.claims.drop 0).take 100 = (Leaf54.supplied.drop 0).take 100 := RouteA.same_spec _ _ chunkBool0
#print axioms chunk0
end Proof54

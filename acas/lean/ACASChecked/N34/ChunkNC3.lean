import ACASChecked.N34.NodeDataNC
import ACASChecked.SameSpec
namespace Proof34
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool3 : RouteA.same ((Leaf34.claims.drop 300).take 100) ((Leaf34.supplied.drop 300).take 100) = true := by decide +kernel
theorem chunk3 : (Leaf34.claims.drop 300).take 100 = (Leaf34.supplied.drop 300).take 100 := RouteA.same_spec _ _ chunkBool3
#print axioms chunk3
end Proof34

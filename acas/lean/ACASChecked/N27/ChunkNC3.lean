import ACASChecked.N27.NodeDataNC
import ACASChecked.SameSpec
namespace Proof27
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool3 : RouteA.same ((Leaf27.claims.drop 300).take 100) ((Leaf27.supplied.drop 300).take 100) = true := by decide +kernel
theorem chunk3 : (Leaf27.claims.drop 300).take 100 = (Leaf27.supplied.drop 300).take 100 := RouteA.same_spec _ _ chunkBool3
#print axioms chunk3
end Proof27

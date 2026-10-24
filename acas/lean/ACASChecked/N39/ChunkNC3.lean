import ACASChecked.N39.NodeDataNC
import ACASChecked.SameSpec
namespace Proof39
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool3 : RouteA.same ((Leaf39.claims.drop 300).take 100) ((Leaf39.supplied.drop 300).take 100) = true := by decide +kernel
theorem chunk3 : (Leaf39.claims.drop 300).take 100 = (Leaf39.supplied.drop 300).take 100 := RouteA.same_spec _ _ chunkBool3
#print axioms chunk3
end Proof39

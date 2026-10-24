import ACASChecked.N50.NodeDataNC
import ACASChecked.SameSpec
namespace Proof50
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool0 : RouteA.same ((Leaf50.claims.drop 0).take 100) ((Leaf50.supplied.drop 0).take 100) = true := by decide +kernel
theorem chunk0 : (Leaf50.claims.drop 0).take 100 = (Leaf50.supplied.drop 0).take 100 := RouteA.same_spec _ _ chunkBool0
#print axioms chunk0
end Proof50

import ACASChecked.N17.NodeDataNC
import ACASChecked.SameSpec
namespace Proof17
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool5 : RouteA.same ((Leaf17.claims.drop 500).take 1) ((Leaf17.supplied.drop 500).take 1) = true := by decide +kernel
theorem chunk5 : (Leaf17.claims.drop 500).take 1 = (Leaf17.supplied.drop 500).take 1 := RouteA.same_spec _ _ chunkBool5
#print axioms chunk5
end Proof17

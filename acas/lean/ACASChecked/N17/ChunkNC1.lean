import ACASChecked.N17.NodeDataNC
import ACASChecked.SameSpec
namespace Proof17
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool1 : RouteA.same ((Leaf17.claims.drop 100).take 100) ((Leaf17.supplied.drop 100).take 100) = true := by decide +kernel
theorem chunk1 : (Leaf17.claims.drop 100).take 100 = (Leaf17.supplied.drop 100).take 100 := RouteA.same_spec _ _ chunkBool1
#print axioms chunk1
end Proof17

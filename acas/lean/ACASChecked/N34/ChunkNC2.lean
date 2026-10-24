import ACASChecked.N34.NodeDataNC
import ACASChecked.SameSpec
namespace Proof34
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool2 : RouteA.same ((Leaf34.claims.drop 200).take 100) ((Leaf34.supplied.drop 200).take 100) = true := by decide +kernel
theorem chunk2 : (Leaf34.claims.drop 200).take 100 = (Leaf34.supplied.drop 200).take 100 := RouteA.same_spec _ _ chunkBool2
#print axioms chunk2
end Proof34

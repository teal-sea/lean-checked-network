import ACASChecked.N49.NodeDataNC
import ACASChecked.SameSpec
namespace Proof49
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool2 : RouteA.same ((Leaf49.claims.drop 200).take 100) ((Leaf49.supplied.drop 200).take 100) = true := by decide +kernel
theorem chunk2 : (Leaf49.claims.drop 200).take 100 = (Leaf49.supplied.drop 200).take 100 := RouteA.same_spec _ _ chunkBool2
#print axioms chunk2
end Proof49

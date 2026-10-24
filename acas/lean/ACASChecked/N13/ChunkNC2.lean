import ACASChecked.N13.NodeDataNC
import ACASChecked.SameSpec
namespace Proof13
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool2 : RouteA.same ((Leaf13.claims.drop 200).take 100) ((Leaf13.supplied.drop 200).take 100) = true := by decide +kernel
theorem chunk2 : (Leaf13.claims.drop 200).take 100 = (Leaf13.supplied.drop 200).take 100 := RouteA.same_spec _ _ chunkBool2
#print axioms chunk2
end Proof13

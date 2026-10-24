import ACASChecked.N64.NodeDataNC
import ACASChecked.SameSpec
namespace Proof64
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool2 : RouteA.same ((Leaf64.claims.drop 200).take 100) ((Leaf64.supplied.drop 200).take 100) = true := by decide +kernel
theorem chunk2 : (Leaf64.claims.drop 200).take 100 = (Leaf64.supplied.drop 200).take 100 := RouteA.same_spec _ _ chunkBool2
#print axioms chunk2
end Proof64

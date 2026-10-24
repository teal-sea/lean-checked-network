import ACASChecked.N51.NodeDataNC
import ACASChecked.SameSpec
namespace Proof51
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool2 : RouteA.same ((Leaf51.claims.drop 200).take 100) ((Leaf51.supplied.drop 200).take 100) = true := by decide +kernel
theorem chunk2 : (Leaf51.claims.drop 200).take 100 = (Leaf51.supplied.drop 200).take 100 := RouteA.same_spec _ _ chunkBool2
#print axioms chunk2
end Proof51

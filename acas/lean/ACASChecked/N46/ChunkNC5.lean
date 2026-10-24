import ACASChecked.N46.NodeDataNC
import ACASChecked.SameSpec
namespace Proof46
open SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunkBool5 : RouteA.same ((Leaf46.claims.drop 500).take 1) ((Leaf46.supplied.drop 500).take 1) = true := by decide +kernel
theorem chunk5 : (Leaf46.claims.drop 500).take 1 = (Leaf46.supplied.drop 500).take 1 := RouteA.same_spec _ _ chunkBool5
#print axioms chunk5
end Proof46

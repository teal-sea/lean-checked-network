import ACASChecked.N37.ShapeNC
import ACASChecked.N37.PackedNC0
import ACASChecked.N37.EndpointNC0
import ACASChecked.N37.PackedNC1
import ACASChecked.N37.EndpointNC1
import ACASChecked.N37.PackedNC2
import ACASChecked.N37.EndpointNC2
import ACASChecked.N37.PackedNC3
import ACASChecked.N37.EndpointNC3
import ACASChecked.N37.PackedNC4
import ACASChecked.N37.EndpointNC4
import ACASChecked.N37.PackedNC5
import ACASChecked.N37.EndpointNC5
import ACASChecked.N37.MarginNC
namespace Proof37
open SharedWeights
open RouteA Leaf37
theorem node37NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf37.endpoints0 = true ∧ Leaf37.endpoints1 = true ∧ Leaf37.endpoints2 = true ∧ Leaf37.endpoints3 = true ∧ Leaf37.endpoints4 = true ∧ Leaf37.endpoints5 = true ∧ Leaf37.marginCheck = true ∧ Leaf37.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node37NC
end Proof37

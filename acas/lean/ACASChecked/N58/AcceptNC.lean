import ACASChecked.N58.ShapeNC
import ACASChecked.N58.PackedNC0
import ACASChecked.N58.EndpointNC0
import ACASChecked.N58.PackedNC1
import ACASChecked.N58.EndpointNC1
import ACASChecked.N58.PackedNC2
import ACASChecked.N58.EndpointNC2
import ACASChecked.N58.PackedNC3
import ACASChecked.N58.EndpointNC3
import ACASChecked.N58.PackedNC4
import ACASChecked.N58.EndpointNC4
import ACASChecked.N58.PackedNC5
import ACASChecked.N58.EndpointNC5
import ACASChecked.N58.MarginNC
namespace Proof58
open SharedWeights
open RouteA Leaf58
theorem node58NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf58.endpoints0 = true ∧ Leaf58.endpoints1 = true ∧ Leaf58.endpoints2 = true ∧ Leaf58.endpoints3 = true ∧ Leaf58.endpoints4 = true ∧ Leaf58.endpoints5 = true ∧ Leaf58.marginCheck = true ∧ Leaf58.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node58NC
end Proof58

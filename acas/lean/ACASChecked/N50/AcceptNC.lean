import ACASChecked.N50.ShapeNC
import ACASChecked.N50.PackedNC0
import ACASChecked.N50.EndpointNC0
import ACASChecked.N50.PackedNC1
import ACASChecked.N50.EndpointNC1
import ACASChecked.N50.PackedNC2
import ACASChecked.N50.EndpointNC2
import ACASChecked.N50.PackedNC3
import ACASChecked.N50.EndpointNC3
import ACASChecked.N50.PackedNC4
import ACASChecked.N50.EndpointNC4
import ACASChecked.N50.PackedNC5
import ACASChecked.N50.EndpointNC5
import ACASChecked.N50.MarginNC
namespace Proof50
open SharedWeights
open RouteA Leaf50
theorem node50NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf50.endpoints0 = true ∧ Leaf50.endpoints1 = true ∧ Leaf50.endpoints2 = true ∧ Leaf50.endpoints3 = true ∧ Leaf50.endpoints4 = true ∧ Leaf50.endpoints5 = true ∧ Leaf50.marginCheck = true ∧ Leaf50.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node50NC
end Proof50

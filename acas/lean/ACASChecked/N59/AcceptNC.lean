import ACASChecked.N59.ShapeNC
import ACASChecked.N59.PackedNC0
import ACASChecked.N59.EndpointNC0
import ACASChecked.N59.PackedNC1
import ACASChecked.N59.EndpointNC1
import ACASChecked.N59.PackedNC2
import ACASChecked.N59.EndpointNC2
import ACASChecked.N59.PackedNC3
import ACASChecked.N59.EndpointNC3
import ACASChecked.N59.PackedNC4
import ACASChecked.N59.EndpointNC4
import ACASChecked.N59.PackedNC5
import ACASChecked.N59.EndpointNC5
import ACASChecked.N59.MarginNC
namespace Proof59
open SharedWeights
open RouteA Leaf59
theorem node59NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf59.endpoints0 = true ∧ Leaf59.endpoints1 = true ∧ Leaf59.endpoints2 = true ∧ Leaf59.endpoints3 = true ∧ Leaf59.endpoints4 = true ∧ Leaf59.endpoints5 = true ∧ Leaf59.marginCheck = true ∧ Leaf59.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node59NC
end Proof59

import ACASChecked.N63.ShapeNC
import ACASChecked.N63.PackedNC0
import ACASChecked.N63.EndpointNC0
import ACASChecked.N63.PackedNC1
import ACASChecked.N63.EndpointNC1
import ACASChecked.N63.PackedNC2
import ACASChecked.N63.EndpointNC2
import ACASChecked.N63.PackedNC3
import ACASChecked.N63.EndpointNC3
import ACASChecked.N63.PackedNC4
import ACASChecked.N63.EndpointNC4
import ACASChecked.N63.PackedNC5
import ACASChecked.N63.EndpointNC5
import ACASChecked.N63.MarginNC
namespace Proof63
open SharedWeights
open RouteA Leaf63
theorem node63NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf63.endpoints0 = true ∧ Leaf63.endpoints1 = true ∧ Leaf63.endpoints2 = true ∧ Leaf63.endpoints3 = true ∧ Leaf63.endpoints4 = true ∧ Leaf63.endpoints5 = true ∧ Leaf63.marginCheck = true ∧ Leaf63.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node63NC
end Proof63

import ACASChecked.N17.ShapeNC
import ACASChecked.N17.PackedNC0
import ACASChecked.N17.EndpointNC0
import ACASChecked.N17.PackedNC1
import ACASChecked.N17.EndpointNC1
import ACASChecked.N17.PackedNC2
import ACASChecked.N17.EndpointNC2
import ACASChecked.N17.PackedNC3
import ACASChecked.N17.EndpointNC3
import ACASChecked.N17.PackedNC4
import ACASChecked.N17.EndpointNC4
import ACASChecked.N17.PackedNC5
import ACASChecked.N17.EndpointNC5
import ACASChecked.N17.MarginNC
namespace Proof17
open SharedWeights
open RouteA Leaf17
theorem node17NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf17.endpoints0 = true ∧ Leaf17.endpoints1 = true ∧ Leaf17.endpoints2 = true ∧ Leaf17.endpoints3 = true ∧ Leaf17.endpoints4 = true ∧ Leaf17.endpoints5 = true ∧ Leaf17.marginCheck = true ∧ Leaf17.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node17NC
end Proof17

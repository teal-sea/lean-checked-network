import ACASChecked.N40.ShapeNC
import ACASChecked.N40.PackedNC0
import ACASChecked.N40.EndpointNC0
import ACASChecked.N40.PackedNC1
import ACASChecked.N40.EndpointNC1
import ACASChecked.N40.PackedNC2
import ACASChecked.N40.EndpointNC2
import ACASChecked.N40.PackedNC3
import ACASChecked.N40.EndpointNC3
import ACASChecked.N40.PackedNC4
import ACASChecked.N40.EndpointNC4
import ACASChecked.N40.PackedNC5
import ACASChecked.N40.EndpointNC5
import ACASChecked.N40.MarginNC
namespace Proof40
open SharedWeights
open RouteA Leaf40
theorem node40NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf40.endpoints0 = true ∧ Leaf40.endpoints1 = true ∧ Leaf40.endpoints2 = true ∧ Leaf40.endpoints3 = true ∧ Leaf40.endpoints4 = true ∧ Leaf40.endpoints5 = true ∧ Leaf40.marginCheck = true ∧ Leaf40.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node40NC
end Proof40

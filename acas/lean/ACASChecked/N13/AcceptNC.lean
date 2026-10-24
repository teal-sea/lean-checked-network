import ACASChecked.N13.ShapeNC
import ACASChecked.N13.PackedNC0
import ACASChecked.N13.EndpointNC0
import ACASChecked.N13.PackedNC1
import ACASChecked.N13.EndpointNC1
import ACASChecked.N13.PackedNC2
import ACASChecked.N13.EndpointNC2
import ACASChecked.N13.PackedNC3
import ACASChecked.N13.EndpointNC3
import ACASChecked.N13.PackedNC4
import ACASChecked.N13.EndpointNC4
import ACASChecked.N13.PackedNC5
import ACASChecked.N13.EndpointNC5
import ACASChecked.N13.MarginNC
namespace Proof13
open SharedWeights
open RouteA Leaf13
theorem node13NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf13.endpoints0 = true ∧ Leaf13.endpoints1 = true ∧ Leaf13.endpoints2 = true ∧ Leaf13.endpoints3 = true ∧ Leaf13.endpoints4 = true ∧ Leaf13.endpoints5 = true ∧ Leaf13.marginCheck = true ∧ Leaf13.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node13NC
end Proof13

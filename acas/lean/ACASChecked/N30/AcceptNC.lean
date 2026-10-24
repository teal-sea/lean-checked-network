import ACASChecked.N30.ShapeNC
import ACASChecked.N30.PackedNC0
import ACASChecked.N30.EndpointNC0
import ACASChecked.N30.PackedNC1
import ACASChecked.N30.EndpointNC1
import ACASChecked.N30.PackedNC2
import ACASChecked.N30.EndpointNC2
import ACASChecked.N30.PackedNC3
import ACASChecked.N30.EndpointNC3
import ACASChecked.N30.PackedNC4
import ACASChecked.N30.EndpointNC4
import ACASChecked.N30.PackedNC5
import ACASChecked.N30.EndpointNC5
import ACASChecked.N30.MarginNC
namespace Proof30
open SharedWeights
open RouteA Leaf30
theorem node30NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf30.endpoints0 = true ∧ Leaf30.endpoints1 = true ∧ Leaf30.endpoints2 = true ∧ Leaf30.endpoints3 = true ∧ Leaf30.endpoints4 = true ∧ Leaf30.endpoints5 = true ∧ Leaf30.marginCheck = true ∧ Leaf30.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node30NC
end Proof30

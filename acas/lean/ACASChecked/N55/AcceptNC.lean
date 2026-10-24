import ACASChecked.N55.ShapeNC
import ACASChecked.N55.PackedNC0
import ACASChecked.N55.EndpointNC0
import ACASChecked.N55.PackedNC1
import ACASChecked.N55.EndpointNC1
import ACASChecked.N55.PackedNC2
import ACASChecked.N55.EndpointNC2
import ACASChecked.N55.PackedNC3
import ACASChecked.N55.EndpointNC3
import ACASChecked.N55.PackedNC4
import ACASChecked.N55.EndpointNC4
import ACASChecked.N55.PackedNC5
import ACASChecked.N55.EndpointNC5
import ACASChecked.N55.MarginNC
namespace Proof55
open SharedWeights
open RouteA Leaf55
theorem node55NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf55.endpoints0 = true ∧ Leaf55.endpoints1 = true ∧ Leaf55.endpoints2 = true ∧ Leaf55.endpoints3 = true ∧ Leaf55.endpoints4 = true ∧ Leaf55.endpoints5 = true ∧ Leaf55.marginCheck = true ∧ Leaf55.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node55NC
end Proof55

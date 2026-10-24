import ACASChecked.N54.ShapeNC
import ACASChecked.N54.PackedNC0
import ACASChecked.N54.EndpointNC0
import ACASChecked.N54.PackedNC1
import ACASChecked.N54.EndpointNC1
import ACASChecked.N54.PackedNC2
import ACASChecked.N54.EndpointNC2
import ACASChecked.N54.PackedNC3
import ACASChecked.N54.EndpointNC3
import ACASChecked.N54.PackedNC4
import ACASChecked.N54.EndpointNC4
import ACASChecked.N54.PackedNC5
import ACASChecked.N54.EndpointNC5
import ACASChecked.N54.MarginNC
namespace Proof54
open SharedWeights
open RouteA Leaf54
theorem node54NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf54.endpoints0 = true ∧ Leaf54.endpoints1 = true ∧ Leaf54.endpoints2 = true ∧ Leaf54.endpoints3 = true ∧ Leaf54.endpoints4 = true ∧ Leaf54.endpoints5 = true ∧ Leaf54.marginCheck = true ∧ Leaf54.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node54NC
end Proof54

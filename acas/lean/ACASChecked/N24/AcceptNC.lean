import ACASChecked.N24.ShapeNC
import ACASChecked.N24.PackedNC0
import ACASChecked.N24.EndpointNC0
import ACASChecked.N24.PackedNC1
import ACASChecked.N24.EndpointNC1
import ACASChecked.N24.PackedNC2
import ACASChecked.N24.EndpointNC2
import ACASChecked.N24.PackedNC3
import ACASChecked.N24.EndpointNC3
import ACASChecked.N24.PackedNC4
import ACASChecked.N24.EndpointNC4
import ACASChecked.N24.PackedNC5
import ACASChecked.N24.EndpointNC5
import ACASChecked.N24.MarginNC
namespace Proof24
open SharedWeights
open RouteA Leaf24
theorem node24NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf24.endpoints0 = true ∧ Leaf24.endpoints1 = true ∧ Leaf24.endpoints2 = true ∧ Leaf24.endpoints3 = true ∧ Leaf24.endpoints4 = true ∧ Leaf24.endpoints5 = true ∧ Leaf24.marginCheck = true ∧ Leaf24.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node24NC
end Proof24

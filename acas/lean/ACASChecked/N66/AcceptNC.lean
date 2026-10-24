import ACASChecked.N66.ShapeNC
import ACASChecked.N66.PackedNC0
import ACASChecked.N66.EndpointNC0
import ACASChecked.N66.PackedNC1
import ACASChecked.N66.EndpointNC1
import ACASChecked.N66.PackedNC2
import ACASChecked.N66.EndpointNC2
import ACASChecked.N66.PackedNC3
import ACASChecked.N66.EndpointNC3
import ACASChecked.N66.PackedNC4
import ACASChecked.N66.EndpointNC4
import ACASChecked.N66.PackedNC5
import ACASChecked.N66.EndpointNC5
import ACASChecked.N66.MarginNC
namespace Proof66
open SharedWeights
open RouteA Leaf66
theorem node66NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf66.endpoints0 = true ∧ Leaf66.endpoints1 = true ∧ Leaf66.endpoints2 = true ∧ Leaf66.endpoints3 = true ∧ Leaf66.endpoints4 = true ∧ Leaf66.endpoints5 = true ∧ Leaf66.marginCheck = true ∧ Leaf66.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node66NC
end Proof66

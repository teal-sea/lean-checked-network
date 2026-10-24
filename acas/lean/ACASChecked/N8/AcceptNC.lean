import ACASChecked.N8.ShapeNC
import ACASChecked.N8.PackedNC0
import ACASChecked.N8.EndpointNC0
import ACASChecked.N8.PackedNC1
import ACASChecked.N8.EndpointNC1
import ACASChecked.N8.PackedNC2
import ACASChecked.N8.EndpointNC2
import ACASChecked.N8.PackedNC3
import ACASChecked.N8.EndpointNC3
import ACASChecked.N8.PackedNC4
import ACASChecked.N8.EndpointNC4
import ACASChecked.N8.PackedNC5
import ACASChecked.N8.EndpointNC5
import ACASChecked.N8.MarginNC
namespace Proof8
open SharedWeights
open RouteA Leaf8
theorem node8NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf8.endpoints0 = true ∧ Leaf8.endpoints1 = true ∧ Leaf8.endpoints2 = true ∧ Leaf8.endpoints3 = true ∧ Leaf8.endpoints4 = true ∧ Leaf8.endpoints5 = true ∧ Leaf8.marginCheck = true ∧ Leaf8.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node8NC
end Proof8

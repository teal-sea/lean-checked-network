import ACASChecked.N38.ShapeNC
import ACASChecked.N38.PackedNC0
import ACASChecked.N38.EndpointNC0
import ACASChecked.N38.PackedNC1
import ACASChecked.N38.EndpointNC1
import ACASChecked.N38.PackedNC2
import ACASChecked.N38.EndpointNC2
import ACASChecked.N38.PackedNC3
import ACASChecked.N38.EndpointNC3
import ACASChecked.N38.PackedNC4
import ACASChecked.N38.EndpointNC4
import ACASChecked.N38.PackedNC5
import ACASChecked.N38.EndpointNC5
import ACASChecked.N38.MarginNC
namespace Proof38
open SharedWeights
open RouteA Leaf38
theorem node38NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf38.endpoints0 = true ∧ Leaf38.endpoints1 = true ∧ Leaf38.endpoints2 = true ∧ Leaf38.endpoints3 = true ∧ Leaf38.endpoints4 = true ∧ Leaf38.endpoints5 = true ∧ Leaf38.marginCheck = true ∧ Leaf38.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node38NC
end Proof38

import ACASChecked.N49.ShapeNC
import ACASChecked.N49.PackedNC0
import ACASChecked.N49.EndpointNC0
import ACASChecked.N49.PackedNC1
import ACASChecked.N49.EndpointNC1
import ACASChecked.N49.PackedNC2
import ACASChecked.N49.EndpointNC2
import ACASChecked.N49.PackedNC3
import ACASChecked.N49.EndpointNC3
import ACASChecked.N49.PackedNC4
import ACASChecked.N49.EndpointNC4
import ACASChecked.N49.PackedNC5
import ACASChecked.N49.EndpointNC5
import ACASChecked.N49.MarginNC
namespace Proof49
open SharedWeights
open RouteA Leaf49
theorem node49NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf49.endpoints0 = true ∧ Leaf49.endpoints1 = true ∧ Leaf49.endpoints2 = true ∧ Leaf49.endpoints3 = true ∧ Leaf49.endpoints4 = true ∧ Leaf49.endpoints5 = true ∧ Leaf49.marginCheck = true ∧ Leaf49.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node49NC
end Proof49

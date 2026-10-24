import ACASChecked.N34.ShapeNC
import ACASChecked.N34.PackedNC0
import ACASChecked.N34.EndpointNC0
import ACASChecked.N34.PackedNC1
import ACASChecked.N34.EndpointNC1
import ACASChecked.N34.PackedNC2
import ACASChecked.N34.EndpointNC2
import ACASChecked.N34.PackedNC3
import ACASChecked.N34.EndpointNC3
import ACASChecked.N34.PackedNC4
import ACASChecked.N34.EndpointNC4
import ACASChecked.N34.PackedNC5
import ACASChecked.N34.EndpointNC5
import ACASChecked.N34.MarginNC
namespace Proof34
open SharedWeights
open RouteA Leaf34
theorem node34NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf34.endpoints0 = true ∧ Leaf34.endpoints1 = true ∧ Leaf34.endpoints2 = true ∧ Leaf34.endpoints3 = true ∧ Leaf34.endpoints4 = true ∧ Leaf34.endpoints5 = true ∧ Leaf34.marginCheck = true ∧ Leaf34.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node34NC
end Proof34

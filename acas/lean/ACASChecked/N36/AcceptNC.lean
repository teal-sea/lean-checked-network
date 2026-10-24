import ACASChecked.N36.ShapeNC
import ACASChecked.N36.PackedNC0
import ACASChecked.N36.EndpointNC0
import ACASChecked.N36.PackedNC1
import ACASChecked.N36.EndpointNC1
import ACASChecked.N36.PackedNC2
import ACASChecked.N36.EndpointNC2
import ACASChecked.N36.PackedNC3
import ACASChecked.N36.EndpointNC3
import ACASChecked.N36.PackedNC4
import ACASChecked.N36.EndpointNC4
import ACASChecked.N36.PackedNC5
import ACASChecked.N36.EndpointNC5
import ACASChecked.N36.MarginNC
namespace Proof36
open SharedWeights
open RouteA Leaf36
theorem node36NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf36.endpoints0 = true ∧ Leaf36.endpoints1 = true ∧ Leaf36.endpoints2 = true ∧ Leaf36.endpoints3 = true ∧ Leaf36.endpoints4 = true ∧ Leaf36.endpoints5 = true ∧ Leaf36.marginCheck = true ∧ Leaf36.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node36NC
end Proof36

import ACASChecked.N65.ShapeNC
import ACASChecked.N65.PackedNC0
import ACASChecked.N65.EndpointNC0
import ACASChecked.N65.PackedNC1
import ACASChecked.N65.EndpointNC1
import ACASChecked.N65.PackedNC2
import ACASChecked.N65.EndpointNC2
import ACASChecked.N65.PackedNC3
import ACASChecked.N65.EndpointNC3
import ACASChecked.N65.PackedNC4
import ACASChecked.N65.EndpointNC4
import ACASChecked.N65.PackedNC5
import ACASChecked.N65.EndpointNC5
import ACASChecked.N65.MarginNC
namespace Proof65
open SharedWeights
open RouteA Leaf65
theorem node65NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf65.endpoints0 = true ∧ Leaf65.endpoints1 = true ∧ Leaf65.endpoints2 = true ∧ Leaf65.endpoints3 = true ∧ Leaf65.endpoints4 = true ∧ Leaf65.endpoints5 = true ∧ Leaf65.marginCheck = true ∧ Leaf65.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node65NC
end Proof65

import ACASChecked.N29.ShapeNC
import ACASChecked.N29.PackedNC0
import ACASChecked.N29.EndpointNC0
import ACASChecked.N29.PackedNC1
import ACASChecked.N29.EndpointNC1
import ACASChecked.N29.PackedNC2
import ACASChecked.N29.EndpointNC2
import ACASChecked.N29.PackedNC3
import ACASChecked.N29.EndpointNC3
import ACASChecked.N29.PackedNC4
import ACASChecked.N29.EndpointNC4
import ACASChecked.N29.PackedNC5
import ACASChecked.N29.EndpointNC5
import ACASChecked.N29.MarginNC
namespace Proof29
open SharedWeights
open RouteA Leaf29
theorem node29NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf29.endpoints0 = true ∧ Leaf29.endpoints1 = true ∧ Leaf29.endpoints2 = true ∧ Leaf29.endpoints3 = true ∧ Leaf29.endpoints4 = true ∧ Leaf29.endpoints5 = true ∧ Leaf29.marginCheck = true ∧ Leaf29.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node29NC
end Proof29

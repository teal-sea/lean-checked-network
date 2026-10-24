import ACASChecked.N42.ShapeNC
import ACASChecked.N42.PackedNC0
import ACASChecked.N42.EndpointNC0
import ACASChecked.N42.PackedNC1
import ACASChecked.N42.EndpointNC1
import ACASChecked.N42.PackedNC2
import ACASChecked.N42.EndpointNC2
import ACASChecked.N42.PackedNC3
import ACASChecked.N42.EndpointNC3
import ACASChecked.N42.PackedNC4
import ACASChecked.N42.EndpointNC4
import ACASChecked.N42.PackedNC5
import ACASChecked.N42.EndpointNC5
import ACASChecked.N42.MarginNC
namespace Proof42
open SharedWeights
open RouteA Leaf42
theorem node42NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf42.endpoints0 = true ∧ Leaf42.endpoints1 = true ∧ Leaf42.endpoints2 = true ∧ Leaf42.endpoints3 = true ∧ Leaf42.endpoints4 = true ∧ Leaf42.endpoints5 = true ∧ Leaf42.marginCheck = true ∧ Leaf42.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node42NC
end Proof42

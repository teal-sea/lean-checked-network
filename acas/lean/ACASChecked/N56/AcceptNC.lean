import ACASChecked.N56.ShapeNC
import ACASChecked.N56.PackedNC0
import ACASChecked.N56.EndpointNC0
import ACASChecked.N56.PackedNC1
import ACASChecked.N56.EndpointNC1
import ACASChecked.N56.PackedNC2
import ACASChecked.N56.EndpointNC2
import ACASChecked.N56.PackedNC3
import ACASChecked.N56.EndpointNC3
import ACASChecked.N56.PackedNC4
import ACASChecked.N56.EndpointNC4
import ACASChecked.N56.PackedNC5
import ACASChecked.N56.EndpointNC5
import ACASChecked.N56.MarginNC
namespace Proof56
open SharedWeights
open RouteA Leaf56
theorem node56NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf56.endpoints0 = true ∧ Leaf56.endpoints1 = true ∧ Leaf56.endpoints2 = true ∧ Leaf56.endpoints3 = true ∧ Leaf56.endpoints4 = true ∧ Leaf56.endpoints5 = true ∧ Leaf56.marginCheck = true ∧ Leaf56.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node56NC
end Proof56

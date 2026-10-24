import ACASChecked.N51.ShapeNC
import ACASChecked.N51.PackedNC0
import ACASChecked.N51.EndpointNC0
import ACASChecked.N51.PackedNC1
import ACASChecked.N51.EndpointNC1
import ACASChecked.N51.PackedNC2
import ACASChecked.N51.EndpointNC2
import ACASChecked.N51.PackedNC3
import ACASChecked.N51.EndpointNC3
import ACASChecked.N51.PackedNC4
import ACASChecked.N51.EndpointNC4
import ACASChecked.N51.PackedNC5
import ACASChecked.N51.EndpointNC5
import ACASChecked.N51.MarginNC
namespace Proof51
open SharedWeights
open RouteA Leaf51
theorem node51NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf51.endpoints0 = true ∧ Leaf51.endpoints1 = true ∧ Leaf51.endpoints2 = true ∧ Leaf51.endpoints3 = true ∧ Leaf51.endpoints4 = true ∧ Leaf51.endpoints5 = true ∧ Leaf51.marginCheck = true ∧ Leaf51.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node51NC
end Proof51

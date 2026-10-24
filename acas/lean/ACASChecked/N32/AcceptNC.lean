import ACASChecked.N32.ShapeNC
import ACASChecked.N32.PackedNC0
import ACASChecked.N32.EndpointNC0
import ACASChecked.N32.PackedNC1
import ACASChecked.N32.EndpointNC1
import ACASChecked.N32.PackedNC2
import ACASChecked.N32.EndpointNC2
import ACASChecked.N32.PackedNC3
import ACASChecked.N32.EndpointNC3
import ACASChecked.N32.PackedNC4
import ACASChecked.N32.EndpointNC4
import ACASChecked.N32.PackedNC5
import ACASChecked.N32.EndpointNC5
import ACASChecked.N32.MarginNC
namespace Proof32
open SharedWeights
open RouteA Leaf32
theorem node32NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf32.endpoints0 = true ∧ Leaf32.endpoints1 = true ∧ Leaf32.endpoints2 = true ∧ Leaf32.endpoints3 = true ∧ Leaf32.endpoints4 = true ∧ Leaf32.endpoints5 = true ∧ Leaf32.marginCheck = true ∧ Leaf32.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node32NC
end Proof32

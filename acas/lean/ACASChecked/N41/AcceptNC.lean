import ACASChecked.N41.ShapeNC
import ACASChecked.N41.PackedNC0
import ACASChecked.N41.EndpointNC0
import ACASChecked.N41.PackedNC1
import ACASChecked.N41.EndpointNC1
import ACASChecked.N41.PackedNC2
import ACASChecked.N41.EndpointNC2
import ACASChecked.N41.PackedNC3
import ACASChecked.N41.EndpointNC3
import ACASChecked.N41.PackedNC4
import ACASChecked.N41.EndpointNC4
import ACASChecked.N41.PackedNC5
import ACASChecked.N41.EndpointNC5
import ACASChecked.N41.MarginNC
namespace Proof41
open SharedWeights
open RouteA Leaf41
theorem node41NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf41.endpoints0 = true ∧ Leaf41.endpoints1 = true ∧ Leaf41.endpoints2 = true ∧ Leaf41.endpoints3 = true ∧ Leaf41.endpoints4 = true ∧ Leaf41.endpoints5 = true ∧ Leaf41.marginCheck = true ∧ Leaf41.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node41NC
end Proof41

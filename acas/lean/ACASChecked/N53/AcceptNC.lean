import ACASChecked.N53.ShapeNC
import ACASChecked.N53.PackedNC0
import ACASChecked.N53.EndpointNC0
import ACASChecked.N53.PackedNC1
import ACASChecked.N53.EndpointNC1
import ACASChecked.N53.PackedNC2
import ACASChecked.N53.EndpointNC2
import ACASChecked.N53.PackedNC3
import ACASChecked.N53.EndpointNC3
import ACASChecked.N53.PackedNC4
import ACASChecked.N53.EndpointNC4
import ACASChecked.N53.PackedNC5
import ACASChecked.N53.EndpointNC5
import ACASChecked.N53.MarginNC
namespace Proof53
open SharedWeights
open RouteA Leaf53
theorem node53NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf53.endpoints0 = true ∧ Leaf53.endpoints1 = true ∧ Leaf53.endpoints2 = true ∧ Leaf53.endpoints3 = true ∧ Leaf53.endpoints4 = true ∧ Leaf53.endpoints5 = true ∧ Leaf53.marginCheck = true ∧ Leaf53.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node53NC
end Proof53

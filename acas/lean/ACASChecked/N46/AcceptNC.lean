import ACASChecked.N46.ShapeNC
import ACASChecked.N46.PackedNC0
import ACASChecked.N46.EndpointNC0
import ACASChecked.N46.PackedNC1
import ACASChecked.N46.EndpointNC1
import ACASChecked.N46.PackedNC2
import ACASChecked.N46.EndpointNC2
import ACASChecked.N46.PackedNC3
import ACASChecked.N46.EndpointNC3
import ACASChecked.N46.PackedNC4
import ACASChecked.N46.EndpointNC4
import ACASChecked.N46.PackedNC5
import ACASChecked.N46.EndpointNC5
import ACASChecked.N46.MarginNC
namespace Proof46
open SharedWeights
open RouteA Leaf46
theorem node46NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf46.endpoints0 = true ∧ Leaf46.endpoints1 = true ∧ Leaf46.endpoints2 = true ∧ Leaf46.endpoints3 = true ∧ Leaf46.endpoints4 = true ∧ Leaf46.endpoints5 = true ∧ Leaf46.marginCheck = true ∧ Leaf46.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node46NC
end Proof46

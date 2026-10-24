import ACASChecked.N39.ShapeNC
import ACASChecked.N39.PackedNC0
import ACASChecked.N39.EndpointNC0
import ACASChecked.N39.PackedNC1
import ACASChecked.N39.EndpointNC1
import ACASChecked.N39.PackedNC2
import ACASChecked.N39.EndpointNC2
import ACASChecked.N39.PackedNC3
import ACASChecked.N39.EndpointNC3
import ACASChecked.N39.PackedNC4
import ACASChecked.N39.EndpointNC4
import ACASChecked.N39.PackedNC5
import ACASChecked.N39.EndpointNC5
import ACASChecked.N39.MarginNC
namespace Proof39
open SharedWeights
open RouteA Leaf39
theorem node39NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf39.endpoints0 = true ∧ Leaf39.endpoints1 = true ∧ Leaf39.endpoints2 = true ∧ Leaf39.endpoints3 = true ∧ Leaf39.endpoints4 = true ∧ Leaf39.endpoints5 = true ∧ Leaf39.marginCheck = true ∧ Leaf39.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node39NC
end Proof39

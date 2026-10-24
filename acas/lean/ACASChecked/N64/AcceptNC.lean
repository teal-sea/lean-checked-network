import ACASChecked.N64.ShapeNC
import ACASChecked.N64.PackedNC0
import ACASChecked.N64.EndpointNC0
import ACASChecked.N64.PackedNC1
import ACASChecked.N64.EndpointNC1
import ACASChecked.N64.PackedNC2
import ACASChecked.N64.EndpointNC2
import ACASChecked.N64.PackedNC3
import ACASChecked.N64.EndpointNC3
import ACASChecked.N64.PackedNC4
import ACASChecked.N64.EndpointNC4
import ACASChecked.N64.PackedNC5
import ACASChecked.N64.EndpointNC5
import ACASChecked.N64.MarginNC
namespace Proof64
open SharedWeights
open RouteA Leaf64
theorem node64NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf64.endpoints0 = true ∧ Leaf64.endpoints1 = true ∧ Leaf64.endpoints2 = true ∧ Leaf64.endpoints3 = true ∧ Leaf64.endpoints4 = true ∧ Leaf64.endpoints5 = true ∧ Leaf64.marginCheck = true ∧ Leaf64.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node64NC
end Proof64

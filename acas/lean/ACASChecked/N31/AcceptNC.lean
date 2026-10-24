import ACASChecked.N31.ShapeNC
import ACASChecked.N31.PackedNC0
import ACASChecked.N31.EndpointNC0
import ACASChecked.N31.PackedNC1
import ACASChecked.N31.EndpointNC1
import ACASChecked.N31.PackedNC2
import ACASChecked.N31.EndpointNC2
import ACASChecked.N31.PackedNC3
import ACASChecked.N31.EndpointNC3
import ACASChecked.N31.PackedNC4
import ACASChecked.N31.EndpointNC4
import ACASChecked.N31.PackedNC5
import ACASChecked.N31.EndpointNC5
import ACASChecked.N31.MarginNC
namespace Proof31
open SharedWeights
open RouteA Leaf31
theorem node31NC : block w0 v0 c0 = true ∧ block w1 v1 c1 = true ∧ block w2 v2 c2 = true ∧ block w3 v3 c3 = true ∧ block w4 v4 c4 = true ∧ block w5 v5 c5 = true ∧ Leaf31.endpoints0 = true ∧ Leaf31.endpoints1 = true ∧ Leaf31.endpoints2 = true ∧ Leaf31.endpoints3 = true ∧ Leaf31.endpoints4 = true ∧ Leaf31.endpoints5 = true ∧ Leaf31.marginCheck = true ∧ Leaf31.claims.length = 501 :=
⟨packedNC0, packedNC1, packedNC2, packedNC3, packedNC4, packedNC5, endpointsNC0, endpointsNC1, endpointsNC2, endpointsNC3, endpointsNC4, endpointsNC5, marginNC, claims_length⟩
#print axioms node31NC
end Proof31

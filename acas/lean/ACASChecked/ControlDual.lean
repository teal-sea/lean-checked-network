import ACASChecked.N8.DataNC0
open RouteA SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace ControlDual
noncomputable def corrupt : List (List Int) → List (List Int)
 | [] => []
 | [] :: rs => [] :: rs
 | (x :: xs) :: rs => (Int.add x 1 :: xs) :: rs
theorem rejected : block w0 (corrupt Leaf8.v0) Leaf8.c0 = false := by decide +kernel
#print axioms rejected
end ControlDual

import ACASChecked.N17.DataNC0
open RouteA SharedWeights
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace ControlWeight
noncomputable def corrupt : List (List Int) → List (List Int)
 | [] => []
 | [] :: rs => [] :: rs
 | (x :: xs) :: rs => (Int.add x 1 :: xs) :: rs
noncomputable def changedWeights := w0.set 0 ((w0.headD []).set 4 (Int.add ((w0.headD []).getD 4 0) 1))
theorem rejected : block changedWeights Leaf17.v0 Leaf17.c0 = false := by decide +kernel
#print axioms rejected
end ControlWeight
